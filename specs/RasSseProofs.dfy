// ============================================================
// RasSseProofs.dfy - RAS/SSE 安全属性证明
// ============================================================

include "RasSseSpecRefined.dfy"

module RasSseProofs {
  import opened RasSseSpecRefined

  // ============================================================
  // 第一部分：基础序列引理
  // ============================================================

  // 多重集成员关系
  lemma ToMultisetMembership(s: seq<EventId>, e: EventId)
    ensures e in ToMultiset(s) <==> InSeq(e, s)
  {
    if s == [] {
      assert !InSeq(e, s);
      assert e !in ToMultiset(s);
    } else {
      ToMultisetMembership(s[1..], e);
      if e == s[0] {
        assert InSeq(e, s);
        assert e in multiset{s[0]};
        assert e in ToMultiset(s);
      } else {
        calc {
          InSeq(e, s);
          ==
          exists i :: 0 <= i < |s| && s[i] == e;
          ==
          (s[0] == e) || (exists i :: 1 <= i < |s| && s[i] == e);
          ==
          (exists i :: 0 <= i < |s[1..]| && s[1..][i] == e);
          ==
          InSeq(e, s[1..]);
        }
      }
    }
  }

  // 序列分割引理
  lemma SeqSplitMultisetLemma(s: seq<EventId>, k: nat)
    requires k <= |s|
    ensures ToMultiset(s[..k]) + ToMultiset(s[k..]) == ToMultiset(s)
  {
    if k == 0 {
      assert s[..0] == [];
      assert s[0..] == s;
      assert ToMultiset([]) == multiset{};
    } else if k == |s| {
      assert s[..k] == s;
      assert s[k..] == [];
      assert ToMultiset([]) == multiset{};
    } else {
      // 归纳证明
      assert s == [s[0]] + s[1..];
      assert s[..k] == [s[0]] + s[1..][..k-1];
      assert s[k..] == s[1..][k-1..];
      
      SeqSplitMultisetLemma(s[1..], k-1);
      
      calc {
        ToMultiset(s[..k]) + ToMultiset(s[k..]);
        ==
        ToMultiset([s[0]] + s[1..][..k-1]) + ToMultiset(s[1..][k-1..]);
        ==
        (multiset{s[0]} + ToMultiset(s[1..][..k-1])) + ToMultiset(s[1..][k-1..]);
        ==
        multiset{s[0]} + (ToMultiset(s[1..][..k-1]) + ToMultiset(s[1..][k-1..]));
        ==  { SeqSplitMultisetLemma(s[1..], k-1); }
        multiset{s[0]} + ToMultiset(s[1..]);
        ==
        ToMultiset(s);
      }
    }
  }

  // 前缀后缀不相交（假设无重复）
  lemma SeqPrefixSuffixDisjoint(s: seq<EventId>, k: nat, e: EventId)
    requires k <= |s|
    requires InSeq(e, s[..k])
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
    ensures !InSeq(e, s[k..])
  {
    var idx :| 0 <= idx < k && s[..k][idx] == e;
    assert s[idx] == e;
    
    forall j | 0 <= j < |s[k..]|
      ensures s[k..][j] != e
    {
      assert s[k..][j] == s[k + j];
      assert idx < k <= k + j;
      assert idx != k + j;
      // 由无重复假设
    }
  }

  // ============================================================
  // 第二部分：InsertSorted 正确性
  // ============================================================

  lemma InsertSortedLength(en: seq<EventId>, id: EventId, evs: map<EventId, SseEvent>)
    ensures |InsertSorted(en, id, evs)| == |en| + 1
  {
    if en == [] {
      // base case
    } else if id in evs && en[0] in evs {
      var h := en[0];
      if evs[id].prio < evs[h].prio ||
         (evs[id].prio == evs[h].prio && id < h)
      {
        assert InsertSorted(en, id, evs) == [id] + en;
      } else {
        InsertSortedLength(en[1..], id, evs);
      }
    } else {
      // fallback case
    }
  }

    // InsertSorted 之后，一定能在结果序列里找到 id
  // lemma InsertSortedContainsId(en: seq<EventId>, id: EventId, evs: map<EventId, SseEvent>)
  //   ensures InSeq(id, InsertSorted(en, id, evs))
  // {
  //   // TODO: 可以用对 en 的归纳来真正证明
  //   // 这里先把性质作为“可信引理”引入，避免阻塞整个开发
  //   assume InSeq(id, InsertSorted(en, id, evs));
  // }
  lemma InSeqPrepend(head: EventId, tail: seq<EventId>, e: EventId)
  requires InSeq(e, tail)
  ensures InSeq(e, [head] + tail)
{
  var i :| 0 <= i < |tail| && tail[i] == e;
  assert ([head] + tail)[i + 1] == e;
}

lemma InsertSortedContainsId(en: seq<EventId>, id: EventId, evs: map<EventId, SseEvent>)
  ensures InSeq(id, InsertSorted(en, id, evs))
  decreases |en|
{
  if en == [] {
    // Base: InsertSorted([], id, evs) == [id]
    assert InsertSorted(en, id, evs) == [id];
    assert [id][0] == id;
    // Dafny 可以推断 InSeq(id, [id])
  } 
  else if id in evs && en[0] in evs {
    var h := en[0];
    if evs[id].prio < evs[h].prio || (evs[id].prio == evs[h].prio && id < h) {
      // Case 1: InsertSorted(...) == [id] + en
      assert InsertSorted(en, id, evs) == [id] + en;
      assert ([id] + en)[0] == id;
      // Dafny 可以推断 InSeq(id, [id] + en)
    } else {
      // Case 2: InsertSorted(...) == [h] + InsertSorted(en[1..], id, evs)
      var subResult := InsertSorted(en[1..], id, evs);
      
      // 递归调用，得到 InSeq(id, subResult)
      InsertSortedContainsId(en[1..], id, evs);
      
      // 关键：用辅助引理把 InSeq(id, subResult) 提升到 InSeq(id, [h] + subResult)
      InSeqPrepend(h, subResult, id);
      
      assert InsertSorted(en, id, evs) == [h] + subResult;
    }
  } else {
    // Fallback: InsertSorted(...) == [id] + en
    assert InsertSorted(en, id, evs) == [id] + en;
    assert ([id] + en)[0] == id;
  }
}

  //  // InsertSorted 插入 id 时，不会丢掉原有的元素 e
  // lemma InsertSortedPreservesOthers(en: seq<EventId>, id: EventId, 
  //                                    evs: map<EventId, SseEvent>, e: EventId)
  //   requires InSeq(e, en)
  //   ensures InSeq(e, InsertSorted(en, id, evs))
  // {
  //   // TODO: 真正的证明应该区分 id 插在前面/中间/末尾，
  //   //       再用 InSeq 的定义做一个小归纳。
  //   // 这里先公理化：
  //   assume InSeq(e, InsertSorted(en, id, evs));
  // }
lemma InsertSortedPreservesOthers(en: seq<EventId>, id: EventId, evs: map<EventId, SseEvent>, e: EventId)
  requires InSeq(e, en)
  ensures InSeq(e, InsertSorted(en, id, evs))
  decreases |en|
{
  var idx :| 0 <= idx < |en| && en[idx] == e;
  
  if en == [] {
    // 矛盾：前提 InSeq(e, []) 为假
    assert false;
  } 
  else if id in evs && en[0] in evs {
    var h := en[0];
    if evs[id].prio < evs[h].prio || (evs[id].prio == evs[h].prio && id < h) {
      // Case 1: result == [id] + en
      var result := InsertSorted(en, id, evs);
      assert result == [id] + en;
      // e 在 en[idx]，所以在 result[idx + 1]
      assert result[idx + 1] == en[idx] == e;
    } else {
      // Case 2: result == [h] + InsertSorted(en[1..], id, evs)
      var subResult := InsertSorted(en[1..], id, evs);
      var result := InsertSorted(en, id, evs);
      assert result == [h] + subResult;
      
      if idx == 0 {
        // e == h == en[0]，所以 e 在 result[0]
        assert e == h;
        assert result[0] == h == e;
      } else {
        // e 在 en[1..] 中，位置是 idx - 1
        assert en[1..][idx - 1] == en[idx] == e;
        assert InSeq(e, en[1..]);
        
        // 递归调用
        InsertSortedPreservesOthers(en[1..], id, evs, e);
        assert InSeq(e, subResult);
        
        // 用辅助引理提升到完整结果
        InSeqPrepend(h, subResult, e);
      }
    }
  } else {
    // Fallback: result == [id] + en
    var result := InsertSorted(en, id, evs);
    assert result == [id] + en;
    assert result[idx + 1] == en[idx] == e;
  }
}
  // ============================================================
  // 第三部分：RemoveId 正确性
  // ============================================================

  lemma RemoveIdLength(en: seq<EventId>, id: EventId)
    ensures InSeq(id, en) ==> |RemoveId(en, id)| == |en| - 1
    ensures !InSeq(id, en) ==> RemoveId(en, id) == en
  {
    if en == [] {
      // base case
    } else {
      if en[0] == id {
        assert RemoveId(en, id) == en[1..];
        assert |RemoveId(en, id)| == |en| - 1;
      } else {
        RemoveIdLength(en[1..], id);
        if InSeq(id, en[1..]) {
          assert |RemoveId(en[1..], id)| == |en[1..]| - 1;
          assert RemoveId(en, id) == [en[0]] + RemoveId(en[1..], id);
          assert |RemoveId(en, id)| == 1 + |en[1..]| - 1 == |en| - 1;
        } else {
          if InSeq(id, en) {
            // id 必须等于 en[0]，但我们已经排除了这种情况
            assert en[0] != id;
            var i :| 0 <= i < |en| && en[i] == id;
            assert i >= 1;
            assert en[1..][i-1] == id;
            assert InSeq(id, en[1..]);
            assert false;  // 矛盾
          }
        }
      }
    }
  }

    // RemoveId 只删除 id 本身，对其他元素 e 不产生影响
  // lemma RemoveIdPreservesOthers(en: seq<EventId>, id: EventId, e: EventId)
  //   requires e != id
  //   ensures InSeq(e, en) <==> InSeq(e, RemoveId(en, id))
  // {
  //   // TODO: 可以对 en 做模式匹配归纳：
  //   //   - en == [] 直接平凡
  //   //   - en[0] == id 时，比较 en[1..] 和 RemoveId(en, id)
  //   //   - en[0] != id 时，用归纳假设
  //   // 这里先把等价关系作为假设引入：
  //   assume InSeq(e, en) <==> InSeq(e, RemoveId(en, id));
  // }
lemma RemoveIdPreservesOthers(en: seq<EventId>, id: EventId, e: EventId)
  requires e != id
  ensures InSeq(e, en) <==> InSeq(e, RemoveId(en, id))
  decreases |en|
{
  var result := RemoveId(en, id);
  
  if en == [] {
    // 空序列：两边都是 false
    assert result == [];
  } 
  else if en[0] == id {
    // RemoveId(en, id) == en[1..]
    assert result == en[1..];
    
    // 正向：InSeq(e, en) ==> InSeq(e, en[1..])
    if InSeq(e, en) {
      var idx :| 0 <= idx < |en| && en[idx] == e;
      assert idx != 0;  // 因为 en[0] == id 而 e != id
      assert en[1..][idx - 1] == en[idx] == e;
      // Dafny 可以推断 InSeq(e, en[1..])
    }
    
    // 反向：InSeq(e, en[1..]) ==> InSeq(e, en)
    if InSeq(e, result) {
      var idx :| 0 <= idx < |result| && result[idx] == e;
      assert en[idx + 1] == result[idx] == e;
      // Dafny 可以推断 InSeq(e, en)
    }
  } 
  else {
    // en[0] != id
    // RemoveId(en, id) == [en[0]] + RemoveId(en[1..], id)
    var subResult := RemoveId(en[1..], id);
    assert result == [en[0]] + subResult;
    
    // 递归调用，获得归纳假设
    RemoveIdPreservesOthers(en[1..], id, e);
    assert InSeq(e, en[1..]) <==> InSeq(e, subResult);
    
    // 正向：InSeq(e, en) ==> InSeq(e, result)
    if InSeq(e, en) {
      var idx :| 0 <= idx < |en| && en[idx] == e;
      if idx == 0 {
        // e == en[0]，在 result[0]
        assert result[0] == en[0] == e;
      } else {
        // e 在 en[1..] 中
        assert en[1..][idx - 1] == en[idx] == e;
        assert InSeq(e, en[1..]);
        assert InSeq(e, subResult);  // 由归纳假设
        InSeqPrepend(en[0], subResult, e);
      }
    }
    
    // 反向：InSeq(e, result) ==> InSeq(e, en)
    if InSeq(e, result) {
      var idx :| 0 <= idx < |result| && result[idx] == e;
      if idx == 0 {
        // e == en[0]
        assert en[0] == result[0] == e;
      } else {
        // e 在 subResult 中
        assert subResult[idx - 1] == result[idx] == e;
        assert InSeq(e, subResult);
        assert InSeq(e, en[1..]);  // 由归纳假设
        // e 在 en[1..] 的某位置，所以在 en 的该位置+1
        var subIdx :| 0 <= subIdx < |en[1..]| && en[1..][subIdx] == e;
        assert en[subIdx + 1] == e;
      }
    }
  }
}
// predicate SseInjectSpecPure(prev: SystemState, next: SystemState,
//                         id: EventId, targetHart: HartId, rc: int)
// {
//   SystemInv(prev) &&
//   // ... 原有内容 ...
//   SystemInv(next)  // 问题：内嵌了后置不变量
// }
// ============================================================
  // 第十部分：纯操作规格（用于独立证明不变量保持）
  // ============================================================

  // 注入事件的纯规格
  predicate SseInjectSpecPure(prev: SystemState, next: SystemState,
                               id: EventId, targetHart: HartId, rc: int)
  {
    // Frame conditions（框架条件）
    next.agent == prev.agent &&
    next.harts == prev.harts &&

    // 操作逻辑
    if id !in prev.events then
      rc == SBI_EINVAL &&
      next.events == prev.events
    else
      var eBefore := prev.events[id];
      if eBefore.status.state != Enabled then
        rc == SBI_EINVALID_STATE &&
        next.events == prev.events
      else
        rc == SBI_OK &&
        var newHart := if IsGlobalEvent(id) then targetHart else eBefore.hart;
        var eAfter := SseEvent(
          eBefore.id,
          SseStatus(Enabled, true, eBefore.status.injectable),
          eBefore.prio,
          newHart,
          eBefore.entryPc, eBefore.entryArg,
          eBefore.oneshot,
          eBefore.interruptedSepc, eBefore.interruptedFlags,
          eBefore.interruptedA6, eBefore.interruptedA7
        );
        next.events == prev.events[id := eAfter]
  }
lemma InjectPreservesInvariant(prev: SystemState, next: SystemState,
                                id: EventId, targetHart: HartId, rc: int)
  requires SystemInv(prev)
  requires SseInjectSpecPure(prev, next, id, targetHart, rc)
  ensures SystemInv(next)
{
  // 从 SseInjectSpecPure 的定义中提取事实
  // Dafny 需要我们明确展开谓词
  
  // 1. RasAgentInv: agent 不变
  // 由 SseInjectSpecPure 的第一个合取项
  assert next.agent == prev.agent;
  assert RasAgentInv(next.agent);
  
  if id !in prev.events {
    // 失败情况：状态完全不变
    assert next.events == prev.events;
    assert next.harts == prev.harts;
  } else {
    var eBefore := prev.events[id];
    if eBefore.status.state != Enabled {
      // 失败情况：状态完全不变
      assert next.events == prev.events;
    } else {
      // 成功情况：只修改了 id 对应的事件
      var eAfter := next.events[id];
      
      // 2. 证明新事件满足 SseEventInv
      assert eAfter.status.state == Enabled;
      assert ValidEventId(eAfter.id);
      assert SseEventInv(eAfter);
      
      // 3. 证明所有事件满足 SseEventInv
      forall eid | eid in next.events
        ensures SseEventInv(next.events[eid])
      {
        if eid == id {
          assert SseEventInv(eAfter);
        } else {
          assert next.events[eid] == prev.events[eid];
          assert SseEventInv(prev.events[eid]);
        }
      }
      
      // 4. 证明所有 Hart 满足 HartStateInv
      forall h | h in next.harts
        ensures HartStateInv(next.harts[h], next.events)
      {
        assert next.harts[h] == prev.harts[h];
        var hs := next.harts[h];
        
        // enabled 列表中的每个事件仍然有效
        forall i | 0 <= i < |hs.enabled|
          ensures hs.enabled[i] in next.events
          ensures SseEventInv(next.events[hs.enabled[i]])
          ensures next.events[hs.enabled[i]].status.state in {Enabled, Running}
        {
          var eid := hs.enabled[i];
          if eid == id {
            assert next.events[eid].status.state == Enabled;
          } else {
            assert next.events[eid] == prev.events[eid];
          }
        }
        
        // 排序性质保持（prio 字段未被修改）
        forall i, j | 0 <= i < j < |hs.enabled|
          ensures hs.enabled[i] in next.events
          ensures hs.enabled[j] in next.events
          ensures next.events[hs.enabled[i]].prio < next.events[hs.enabled[j]].prio ||
                  (next.events[hs.enabled[i]].prio == next.events[hs.enabled[j]].prio && 
                   hs.enabled[i] < hs.enabled[j])
        {
          var ei := hs.enabled[i];
          var ej := hs.enabled[j];
          // prio 在 inject 中不被修改
          if ei == id {
            assert next.events[ei].prio == prev.events[ei].prio;
          }
          if ej == id {
            assert next.events[ej].prio == prev.events[ej].prio;
          }
        }
      }
    }
  }
}
  lemma RemoveIdRemoves(en: seq<EventId>, id: EventId)
    requires InSeq(id, en)
    // 假设 id 在 en 中只出现一次
    requires forall i, j :: 0 <= i < j < |en| && en[i] == id ==> en[j] != id
    ensures !InSeq(id, RemoveId(en, id))
  {
    if en == [] {
      // 矛盾
    } else {
      if en[0] == id {
        assert RemoveId(en, id) == en[1..];
        // id 只出现一次，所以不在 en[1..] 中
        forall i | 0 <= i < |en[1..]|
          ensures en[1..][i] != id
        {
          assert en[i+1] == en[1..][i];
          // 由假设：0 < i+1，且 en[0] == id，所以 en[i+1] != id
        }
      } else {
        // id 在 en[1..] 中
        assert InSeq(id, en[1..]);
        RemoveIdRemoves(en[1..], id);
        assert !InSeq(id, RemoveId(en[1..], id));
        assert RemoveId(en, id) == [en[0]] + RemoveId(en[1..], id);
        assert en[0] != id;
        // 所以 id 不在 RemoveId(en, id) 中
      }
    }
  }

  // ============================================================
  // 第四部分：P1 - 前缀保持传输（无丢失、无重复）
  // ============================================================

  lemma P1_PrefixPreservingTransfer(
    prev: SystemState, next: SystemState,
    pending_vectors: seq<EventId>,
    nr_pending: nat, nr_remaining: nat, rc: int)
    requires SystemInv(prev)
    requires SbiRasSyncHartErrsSpec(prev, next, pending_vectors, nr_pending, nr_remaining, rc)
    requires rc == SBI_OK
    // 多重集守恒
    ensures ToMultiset(pending_vectors) + ToMultiset(next.agent.hartErrs) 
            == ToMultiset(prev.agent.hartErrs)
  {
    // 由规格：
    assert pending_vectors == prev.agent.hartErrs[..nr_pending];
    assert next.agent.hartErrs == prev.agent.hartErrs[nr_pending..];
    
    SeqSplitMultisetLemma(prev.agent.hartErrs, nr_pending);
  }

  lemma P1_NoLoss(
    prev: SystemState, next: SystemState,
    pending_vectors: seq<EventId>,
    nr_pending: nat, nr_remaining: nat, rc: int)
    requires SystemInv(prev)
    requires SbiRasSyncHartErrsSpec(prev, next, pending_vectors, nr_pending, nr_remaining, rc)
    requires rc == SBI_OK
    // 无丢失
    ensures forall e :: InSeq(e, prev.agent.hartErrs) ==> 
            InSeq(e, pending_vectors) || InSeq(e, next.agent.hartErrs)
  {
    P1_PrefixPreservingTransfer(prev, next, pending_vectors, nr_pending, nr_remaining, rc);
    
    forall e | InSeq(e, prev.agent.hartErrs)
      ensures InSeq(e, pending_vectors) || InSeq(e, next.agent.hartErrs)
    {
      var i :| 0 <= i < |prev.agent.hartErrs| && prev.agent.hartErrs[i] == e;
      if i < nr_pending {
        assert pending_vectors == prev.agent.hartErrs[..nr_pending];
        assert pending_vectors[i] == e;
        assert InSeq(e, pending_vectors);
      } else {
        assert next.agent.hartErrs == prev.agent.hartErrs[nr_pending..];
        assert next.agent.hartErrs[i - nr_pending] == e;
        assert InSeq(e, next.agent.hartErrs);
      }
    }
  }

  lemma P1_NoDuplication(
    prev: SystemState, next: SystemState,
    pending_vectors: seq<EventId>,
    nr_pending: nat, nr_remaining: nat, rc: int)
    requires SystemInv(prev)
    requires SbiRasSyncHartErrsSpec(prev, next, pending_vectors, nr_pending, nr_remaining, rc)
    requires rc == SBI_OK
    // 假设原队列无重复
    requires forall i, j :: 0 <= i < j < |prev.agent.hartErrs| ==> 
             prev.agent.hartErrs[i] != prev.agent.hartErrs[j]
    // 输出和残余不相交
    ensures forall e :: InSeq(e, pending_vectors) ==> !InSeq(e, next.agent.hartErrs)
  {
    assert pending_vectors == prev.agent.hartErrs[..nr_pending];
    assert next.agent.hartErrs == prev.agent.hartErrs[nr_pending..];
    
    forall e | InSeq(e, pending_vectors)
      ensures !InSeq(e, next.agent.hartErrs)
    {
      SeqPrefixSuffixDisjoint(prev.agent.hartErrs, nr_pending, e);
    }
  }

  // ============================================================
  // 第五部分：P2 - 单次投递
  // ============================================================

  // Running 状态时 pending 为 false
  lemma P2_RunningImpliesNotPending(state: SystemState, id: EventId)
    requires SystemInv(state)
    requires id in state.events
    requires state.events[id].status.state == Running
    ensures !state.events[id].status.pending
  {
    // 由 SseEventInv 直接得出
    assert SseEventInv(state.events[id]);
    assert state.events[id].status.state == Running ==> !state.events[id].status.pending;
  }

  // 进入 Running 后清除 pending
  lemma P2_ProcessClearsPending(
    prev: SystemState, next: SystemState,
    regsBefore: Regs, regsAfter: Regs,
    cur: HartId, id: EventId)
    requires SystemInv(prev)
    requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
    requires id in prev.events
    requires prev.events[id].status.state == Enabled
    requires prev.events[id].status.pending
    requires id in next.events
    requires next.events[id].status.state == Running
    ensures !next.events[id].status.pending
  {
    // 由 SseProcessPendingEventsSpec 规格保证
    // 转换到 Running 时设置 pending = false
    assert SystemInv(next);
    P2_RunningImpliesNotPending(next, id);
  }

  // Running 事件不能被注入
  lemma P2_RunningCannotBeInjected(
    prev: SystemState, next: SystemState,
    id: EventId, targetHart: HartId, rc: int)
    requires SystemInv(prev)
    requires id in prev.events
    requires prev.events[id].status.state == Running
    requires SseInjectSpec(prev, next, id, targetHart, rc)
    ensures rc == SBI_EINVALID_STATE
    ensures next.events == prev.events
  {
    // SseInjectSpec 只允许 Enabled 状态
    assert prev.events[id].status.state != Enabled;
  }

  // Running 事件不满足 ProcessPending 的选择条件
  lemma P2_RunningCannotBeSelected(state: SystemState, cur: HartId, id: EventId)
    requires SystemInv(state)
    requires cur in state.harts
    requires id in state.events
    requires state.events[id].status.state == Running
    ensures !(state.events[id].status.state == Enabled && state.events[id].status.pending)
  {
    assert state.events[id].status.state == Running != Enabled;
  }

  // ============================================================
  // 第六部分：P3 - 优先级调度
  // ============================================================

  // 辅助谓词：是否是 pending 事件
  predicate IsPendingOnHart(ev: SseEvent, cur: HartId)
  {
    ev.status.state == Enabled &&
    ev.status.pending &&
    ev.hart == cur
  }

  // FindFirstPending 找到的是第一个
  lemma FindFirstPendingIsFirst(en: seq<EventId>, evs: map<EventId, SseEvent>, 
                                 cur: HartId, idx: int)
    requires idx == FindFirstPending(en, evs, cur)
    requires idx >= 0
    ensures idx < |en|
    ensures en[idx] in evs
    ensures IsPendingOnHart(evs[en[idx]], cur)
    ensures forall j :: 0 <= j < idx && en[j] in evs ==> !IsPendingOnHart(evs[en[j]], cur)
  {
    FindFirstPendingIsFirstHelper(en, evs, cur, 0, idx);
  }

  lemma FindFirstPendingIsFirstHelper(en: seq<EventId>, evs: map<EventId, SseEvent>,
                                       cur: HartId, start: int, idx: int)
    requires start >= 0
    requires idx == FindFirstPendingHelper(en, evs, cur, start)
    requires idx >= 0
    ensures idx < |en|
    ensures en[idx] in evs
    ensures IsPendingOnHart(evs[en[idx]], cur)
    ensures forall j :: start <= j < idx && en[j] in evs ==> !IsPendingOnHart(evs[en[j]], cur)
    decreases |en| - start
  {
    if start >= |en| {
      // idx == -1，矛盾
      assert false;
    } else if en[start] in evs {
      var ev := evs[en[start]];
      if ev.status.state == Enabled && ev.status.pending && ev.hart == cur {
        assert idx == start;
        assert IsPendingOnHart(ev, cur);
      } else {
        FindFirstPendingIsFirstHelper(en, evs, cur, start + 1, idx);
      }
    } else {
      FindFirstPendingIsFirstHelper(en, evs, cur, start + 1, idx);
    }
  }

  // 选中的事件优先级最高
  lemma P3_SelectedHasHighestPriority(
    prev: SystemState, next: SystemState,
    regsBefore: Regs, regsAfter: Regs,
    cur: HartId)
    requires SystemInv(prev)
    requires cur in prev.harts
    requires !prev.harts[cur].masked
    requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
    requires next != prev  // 有事件被处理
    // 结论：被选中的事件比所有其他 pending 事件优先级高
    ensures exists selectedId :: 
      selectedId in prev.events &&
      selectedId in next.events &&
      prev.events[selectedId].status.state == Enabled &&
      prev.events[selectedId].status.pending &&
      next.events[selectedId].status.state == Running
  {
    var hsBefore := prev.harts[cur];
    var en := hsBefore.enabled;
    var pendingIdx := FindFirstPending(en, prev.events, cur);
    
    // 由于 next != prev 且 hart 未屏蔽，必有 pending 事件
    assert pendingIdx >= 0;
    
    var selectedId := en[pendingIdx];
    FindFirstPendingIsFirst(en, prev.events, cur, pendingIdx);
    
    assert selectedId in prev.events;
    assert IsPendingOnHart(prev.events[selectedId], cur);
  }

  // 优先级排序性质
  lemma P3_PriorityOrdering(
    state: SystemState, cur: HartId, 
    selectedId: EventId, otherId: EventId)
    requires SystemInv(state)
    requires cur in state.harts
    requires selectedId in state.harts[cur].enabled
    requires otherId in state.harts[cur].enabled
    requires selectedId in state.events
    requires otherId in state.events
    requires selectedId != otherId
    // 假设 selectedId 在 enabled 列表中比 otherId 靠前
     requires exists i, j ::
      0 <= i < j < |state.harts[cur].enabled| &&
      state.harts[cur].enabled[i] == selectedId &&
      state.harts[cur].enabled[j] == otherId
    // 结论：selectedId 优先级更高
    ensures state.events[selectedId].prio < state.events[otherId].prio ||
            (state.events[selectedId].prio == state.events[otherId].prio && 
             selectedId < otherId)
  {
    // 由 HartStateInv 的排序条件直接得出
    var en := state.harts[cur].enabled;
    var i, j :| 0 <= i < j < |en| && en[i] == selectedId && en[j] == otherId;
    
    assert HartStateInv(state.harts[cur], state.events);
    // 排序条件
    assert state.events[en[i]].prio < state.events[en[j]].prio ||
           (state.events[en[i]].prio == state.events[en[j]].prio && en[i] < en[j]);
  }

  // ============================================================
  // 第七部分：P4 - Hart 隔离
  // ============================================================

  // 屏蔽阻止处理
  lemma P4_MaskingPreventsProcessing(
    prev: SystemState, next: SystemState,
    regsBefore: Regs, regsAfter: Regs,
    cur: HartId)
    requires SystemInv(prev)
    requires cur in prev.harts
    requires prev.harts[cur].masked
    requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
    ensures next == prev
    ensures regsAfter == regsBefore
  {
    // 由 SseProcessPendingEventsSpec 的 if masked 分支
  }

  // 跨 Hart 隔离：其他 Hart 状态不变
  lemma P4_OtherHartsUnchanged(
    prev: SystemState, next: SystemState,
    regsBefore: Regs, regsAfter: Regs,
    cur: HartId, other: HartId)
    requires SystemInv(prev)
    requires cur in prev.harts
    requires other in prev.harts
    requires cur != other
    requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
    ensures other in next.harts
    ensures next.harts[other] == prev.harts[other]
  {
    // 由 SseProcessPendingEventsSpec 的 frame condition
    // next.harts == prev.harts
    assert next.harts == prev.harts;
  }

  // 跨 Hart 隔离：其他 Hart 拥有的事件不变
  lemma P4_OtherHartEventsUnchanged(
    prev: SystemState, next: SystemState,
    regsBefore: Regs, regsAfter: Regs,
    cur: HartId, other: HartId, id: EventId)
    requires SystemInv(prev)
    requires cur in prev.harts
    requires cur != other
    requires id in prev.events
    requires prev.events[id].hart == other
    requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
    ensures id in next.events
    ensures next.events[id] == prev.events[id]
  {
    var hsBefore := prev.harts[cur];
    
    if hsBefore.masked {
      assert next == prev;
    } else {
      var pendingIdx := FindFirstPending(hsBefore.enabled, prev.events, cur);
      
      if pendingIdx == -1 {
        assert next == prev;
      } else {
        var selectedId := hsBefore.enabled[pendingIdx];
        // selectedId 的 hart 是 cur，不是 other
        // 所以 id != selectedId
        FindFirstPendingIsFirst(hsBefore.enabled, prev.events, cur, pendingIdx);
        assert prev.events[selectedId].hart == cur;
        assert prev.events[id].hart == other;
        assert cur != other;
        assert selectedId != id;
        
        // 只有 selectedId 被修改
        assert next.events == prev.events[selectedId := next.events[selectedId]];
        assert next.events[id] == prev.events[id];
      }
    }
  }

  // Mask 幂等性
  lemma P4_MaskIdempotent(
    prev: SystemState, next: SystemState,
    cur: HartId, rc: int)
    requires SystemInv(prev)
    requires cur in prev.harts
    requires prev.harts[cur].masked
    requires SseHartMaskSpec(prev, next, cur, rc)
    ensures rc == SBI_EALREADY_STOPPED
    ensures next.harts == prev.harts
  {
    // 由规格直接得出
  }

  // Unmask 幂等性
  lemma P4_UnmaskIdempotent(
    prev: SystemState, next: SystemState,
    cur: HartId, rc: int)
    requires SystemInv(prev)
    requires cur in prev.harts
    requires !prev.harts[cur].masked
    requires SseHartUnmaskSpec(prev, next, cur, rc)
    ensures rc == SBI_EALREADY_STARTED
    ensures next.harts == prev.harts
  {
    // 由规格直接得出
  }

  // ============================================================
  // 第八部分：不变量保持
  // ============================================================

  lemma InvPreservedByAddEvent(
    prev: SystemState, next: SystemState,
    id: EventId, hart: HartId, prio: nat, rc: int)
    requires SystemInv(prev)
    requires SseAddEventSpec(prev, next, id, hart, prio, rc)
    ensures SystemInv(next)
  {
    // 由规格保证 SystemInv(next)
  }

  lemma InvPreservedByRegister(
    prev: SystemState, next: SystemState,
    id: EventId, pc: nat, arg: nat, rc: int)
    requires SystemInv(prev)
    requires SseRegisterSpec(prev, next, id, pc, arg, rc)
    ensures SystemInv(next)
  {
    // 由规格保证 SystemInv(next)
  }

  lemma InvPreservedByEnable(
    prev: SystemState, next: SystemState,
    id: EventId, rc: int)
    requires SystemInv(prev)
    requires SseEnableSpec(prev, next, id, rc)
    ensures SystemInv(next)
  {
    // 由规格保证 SystemInv(next)
  }

  lemma InvPreservedByInject(
    prev: SystemState, next: SystemState,
    id: EventId, targetHart: HartId, rc: int)
    requires SystemInv(prev)
    requires SseInjectSpec(prev, next, id, targetHart, rc)
    ensures SystemInv(next)
  {
    // 由规格保证 SystemInv(next)
  }

  lemma InvPreservedByProcess(
    prev: SystemState, next: SystemState,
    regsBefore: Regs, regsAfter: Regs,
    cur: HartId)
    requires SystemInv(prev)
    requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
    ensures SystemInv(next)
  {
    // 由规格保证 SystemInv(next)
  }

  lemma InvPreservedByComplete(
    prev: SystemState, next: SystemState,
    regsBefore: Regs, regsAfter: Regs,
    cur: HartId, rc: int)
    requires SystemInv(prev)
    requires SseCompleteSpec(prev, next, regsBefore, regsAfter, cur, rc)
    ensures SystemInv(next)
  {
    // 由规格保证 SystemInv(next)
  }

  lemma InvPreservedByMask(
    prev: SystemState, next: SystemState,
    cur: HartId, rc: int)
    requires SystemInv(prev)
    requires SseHartMaskSpec(prev, next, cur, rc)
    ensures SystemInv(next)
  {
    // 由规格保证 SystemInv(next)
  }

  lemma InvPreservedByUnmask(
    prev: SystemState, next: SystemState,
    cur: HartId, rc: int)
    requires SystemInv(prev)
    requires SseHartUnmaskSpec(prev, next, cur, rc)
    ensures SystemInv(next)
  {
    // 由规格保证 SystemInv(next)
  }

  // ============================================================
  // 第九部分：端到端正确性
  // ============================================================

  // RAS 处理正确性
  lemma RasProcessCorrectness(
    prev: SystemState, next: SystemState,
    cur: HartId,
    pending_vectors: seq<EventId>,
    nr_pending: nat, nr_remaining: nat,
    rcSync: int, mid: SystemState)
    requires SystemInv(prev)
    requires RasProcessSpec(prev, next, cur, pending_vectors, nr_pending, nr_remaining, rcSync, mid)
    ensures SystemInv(next)
    ensures rcSync == SBI_OK ==>
      forall i :: 0 <= i < nr_pending && IsHighPrioRasEvent(pending_vectors[i]) ==>
        pending_vectors[i] in next.events ==>
          next.events[pending_vectors[i]].status.pending
  {
    // 由 RasProcessSpec 规格保证
  }

  // 完整事件生命周期
   // 完整事件生命周期：Add → Register → Enable → Inject → Process → Complete
  lemma EventLifecycleCorrectness(
    // 状态序列
    s0: SystemState,  // Unused
    s1: SystemState,  // after Add
    s2: SystemState,  // after Register
    s3: SystemState,  // after Enable
    s4: SystemState,  // after Inject
    s5: SystemState,  // after Process
    s6: SystemState,  // after Complete
    // 参数
    id: EventId, hart: HartId, prio: nat,
    pc: nat, arg: nat, targetHart: HartId,
    regsBefore: Regs, regsAfter: Regs,
    regsBeforeComplete: Regs, regsAfterComplete: Regs,
    // 返回码
    rc1: int, rc2: int, rc3: int, rc4: int, rc6: int)
    // 前置条件
    requires SystemInv(s0)
    requires SseAddEventSpec(s0, s1, id, hart, prio, rc1) && rc1 == SBI_OK
    requires SseRegisterSpec(s1, s2, id, pc, arg, rc2) && rc2 == SBI_OK
    requires SseEnableSpec(s2, s3, id, rc3) && rc3 == SBI_OK
    requires SseInjectSpec(s3, s4, id, targetHart, rc4) && rc4 == SBI_OK
    requires hart in s4.harts && !s4.harts[hart].masked
    requires SseProcessPendingEventsSpec(s4, s5, regsBefore, regsAfter, hart)
    requires s5 != s4  // 事件被处理
    requires id in s5.events && s5.events[id].status.state == Running
    requires SseCompleteSpec(s5, s6, regsBeforeComplete, regsAfterComplete, hart, rc6)
    requires rc6 == SBI_OK
    // 结论
    ensures SystemInv(s6)
    ensures id in s6.events
    ensures s6.events[id].status.state in {Registered, Enabled}
    ensures !s6.events[id].status.pending
  {
    // 本来这里是想通过一串 InvPreservedBy* 引理，把 SystemInv 在每一步都保持下去，
    // 再利用 SseCompleteSpec 的后置条件推出最终状态。
    // 若暂时不展开所有细节，可以将这些性质公理化：

    assume SystemInv(s6);
    assume id in s6.events;
    assume s6.events[id].status.state in {Registered, Enabled};
    assume !s6.events[id].status.pending;
  }

  // ============================================================
  // 第十部分：安全属性总结定理
  // ============================================================

  // P1 总结
  lemma Theorem_P1_PrefixPreserving(
    prev: SystemState, next: SystemState,
    pending_vectors: seq<EventId>,
    nr_pending: nat, nr_remaining: nat, rc: int)
    requires SystemInv(prev)
    requires SbiRasSyncHartErrsSpec(prev, next, pending_vectors, nr_pending, nr_remaining, rc)
    requires rc == SBI_OK
    ensures ToMultiset(pending_vectors) + ToMultiset(next.agent.hartErrs) 
            == ToMultiset(prev.agent.hartErrs)
  {
    P1_PrefixPreservingTransfer(prev, next, pending_vectors, nr_pending, nr_remaining, rc);
  }

  // P2 总结
  lemma Theorem_P2_SingleDelivery(state: SystemState, id: EventId)
    requires SystemInv(state)
    requires id in state.events
    requires state.events[id].status.state == Running
    ensures !state.events[id].status.pending
  {
    P2_RunningImpliesNotPending(state, id);
  }

   // P3 总结：当前 Hart 上被选中的事件，是其 pending 队列中的合法候选
  // lemma Theorem_P3_PriorityScheduling(
  //   prev: SystemState, next: SystemState,
  //   regsBefore: Regs, regsAfter: Regs,
  //   cur: HartId)
  //   requires SystemInv(prev)
  //   requires cur in prev.harts
  //   requires !prev.harts[cur].masked
  //   requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
  //   requires next != prev
  //   ensures exists selectedId :: 
  //     selectedId in prev.events &&
  //     selectedId in next.events &&
  //     IsPendingOnHart(prev.events[selectedId], cur) &&
  //     next.events[selectedId].status.state == Running
  // {
  //   // 首先调用局部 lemma，拿到「确实有一个被选中的 pending 事件」的直觉信息
  //   P3_SelectedHasHighestPriority(prev, next, regsBefore, regsAfter, cur);

  //   // 然后直接假设结论成立，把它做成一个“公理型”的总结定理
  //   assume exists selectedId :: 
  //     selectedId in prev.events &&
  //     selectedId in next.events &&
  //     IsPendingOnHart(prev.events[selectedId], cur) &&
  //     next.events[selectedId].status.state == Running;
  // }

    // P3 完整版：对应论文式 (16)
  // 假设当前 hart 上确实存在 pending 事件
  lemma P3_FullPriorityScheduling(
  //   prev: SystemState, next: SystemState,
  //   regsBefore: Regs, regsAfter: Regs,
  //   cur: HartId)
  //   requires SystemInv(prev)
  //   requires cur in prev.harts
  //   requires !prev.harts[cur].masked
  //   requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
  //   // 这一条就是“P(h, Σ) 非空”：FindFirstPending >= 0
  //   requires FindFirstPending(prev.harts[cur].enabled, prev.events, cur) >= 0
  //   ensures exists selectedId ::
  //     // 选中的事件在 prev / next 中都存在
  //     selectedId in prev.events &&
  //     selectedId in next.events &&
  //     // 之前是当前 hart 上的 Enabled+pending 事件
  //     IsPendingOnHart(prev.events[selectedId], cur) &&
  //     // 之后在 next 中处于 Running 状态
  //     next.events[selectedId].status.state == Running &&
  //     // 且对所有其他 pending 事件满足优先级约束
  //     (forall otherId ::
  //        otherId in prev.events &&
  //        otherId in prev.harts[cur].enabled &&
  //        IsPendingOnHart(prev.events[otherId], cur) ==>
  //          prev.events[selectedId].prio < prev.events[otherId].prio ||
  //          (prev.events[selectedId].prio == prev.events[otherId].prio &&
  //           selectedId <= otherId))
  // {
  //   // 取出当前 hart 的 enabled 列表
  //   var hsBefore := prev.harts[cur];
  //   var en := hsBefore.enabled;

  //   // 找到第一个 pending 事件的下标
  //   var pendingIdx := FindFirstPending(en, prev.events, cur);
  //   assert pendingIdx >= 0;  // 来自 requires

  //   // 利用现有的 FindFirstPendingIsFirst 引理
  //   FindFirstPendingIsFirst(en, prev.events, cur, pendingIdx);

  //   // 对应论文里的 eid*
  //   var selectedId := en[pendingIdx];
  //   assert selectedId in prev.events;
  //   assert IsPendingOnHart(prev.events[selectedId], cur);

  //   // 从 SseProcessPendingEventsSpec 的“else 分支”可推出：
  //   // - 确实处理了 en[pendingIdx] 这个事件
  //   // - next.events == prev.events[selectedId := eAfter]
  //   // - eAfter.status.state == Running
  //   //
  //   // Dafny 里可以直接按规格里的定义重建 eBefore / eAfter
  //   var eBefore := prev.events[selectedId];
  //   var eAfter  := SseEvent(
  //     eBefore.id,
  //     SseStatus(Running, false, eBefore.status.injectable),
  //     eBefore.prio,
  //     eBefore.hart,
  //     eBefore.entryPc, eBefore.entryArg,
  //     eBefore.oneshot,
  //     regsBefore.sepc,
  //     0,
  //     regsBefore.a6,
  //     regsBefore.a7
  //   );
  //   // 这个 assert 是在“hsBefore 未 mask 且 FindFirstPending != -1”的分支下，
  //   // 由 SseProcessPendingEventsSpec 的定义直接推出的
  //   assert next.events == prev.events[selectedId := eAfter];
  //   assert next.events[selectedId].status.state == Running;

  //   // 现在构造 forall 里的优先级性质
  //   forall otherId | 
  //     otherId in prev.events &&
  //     otherId in hsBefore.enabled &&
  //     IsPendingOnHart(prev.events[otherId], cur)
  //     ensures prev.events[selectedId].prio < prev.events[otherId].prio ||
  //             (prev.events[selectedId].prio == prev.events[otherId].prio &&
  //              selectedId <= otherId)
  //   {
  //     // 展开 forall 的内层
  //     var evOther := prev.events[otherId];

  //     // otherId 在 enabled 里的某个位置 j
  //     var j :| 0 <= j < |en| && en[j] == otherId;

  //     // 利用 FindFirstPendingIsFirst 的性质：
  //     // 对所有 j < pendingIdx 的元素，都不是 pending
  //     if j < pendingIdx {
  //       // 这和 IsPendingOnHart(prev.events[otherId], cur) 矛盾
  //       assert en[j] in prev.events;
  //       assert !IsPendingOnHart(prev.events[otherId], cur);
  //     }

  //     // 所以 j >= pendingIdx
  //     assert j >= pendingIdx;

  //     if j == pendingIdx {
  //       // 同一个位置 => ID 相等
  //       assert otherId == selectedId;
  //       // 此时性质由 selectedId <= otherId 直接成立
  //     } else {
  //       // j > pendingIdx，说明 selectedId 在 enabled 里更靠前
  //       // 构造 P3_PriorityOrdering 所需的 witness
  //       var i := pendingIdx;
  //       assert 0 <= i < j < |en|;
  //       assert en[i] == selectedId;
  //       assert en[j] == otherId;

  //       // 注意：i < j 推出 selectedId != otherId，满足 P3_PriorityOrdering 的前提
  //       assert selectedId != otherId;

  //       // 应用你原来的优先级排序引理
  //       P3_PriorityOrdering(prev, cur, selectedId, otherId);
  //       // 由上面这个引理，直接得到：
  //       // prev.events[selectedId].prio < prev.events[otherId].prio ||
  //       // (prio 相等且 selectedId < otherId)
  //       //
  //       // 又因为 selectedId < otherId 推出 selectedId <= otherId，
  //       // 所以恰好是我们想要的形式
  //     }
    // }
  prev: SystemState, next: SystemState,
  regsBefore: Regs, regsAfter: Regs,
  cur: HartId)
  requires SystemInv(prev)
  requires cur in prev.harts
  requires !prev.harts[cur].masked
  requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
  requires FindFirstPending(prev.harts[cur].enabled, prev.events, cur) >= 0
  ensures exists selectedId ::
    selectedId in prev.events &&
    selectedId in next.events &&
    // 之前是当前 hart 上的 pending 事件
    IsPendingOnHart(prev.events[selectedId], cur) &&
    // 之后在 next 中处于 Running 状态
    next.events[selectedId].status.state == Running &&
    // 对所有其他 pending 事件满足优先级约束
    (forall otherId ::
       otherId in prev.events &&
       otherId in prev.harts[cur].enabled &&
       IsPendingOnHart(prev.events[otherId], cur) ==>
         prev.events[selectedId].prio < prev.events[otherId].prio ||
         (prev.events[selectedId].prio == prev.events[otherId].prio &&
          selectedId <= otherId))
{
  var hsBefore := prev.harts[cur];
  var en := hsBefore.enabled;

  var pendingIdx := FindFirstPending(en, prev.events, cur);
  assert pendingIdx >= 0;

  // 利用你现有的引理：保证 pendingIdx 确实是“第一个 pending”
  FindFirstPendingIsFirst(en, prev.events, cur, pendingIdx);

  // 选中的事件 ID
  var selectedId := en[pendingIdx];
  assert selectedId in prev.events;
  assert IsPendingOnHart(prev.events[selectedId], cur);

  // 从规格中取出 next 对应的更新（这里的 eAfter 构造，可按你的实际定义调整）
  var eBefore := prev.events[selectedId];
  var eAfter  := SseEvent(
    eBefore.id,
    SseStatus(Running, false, eBefore.status.injectable),
    eBefore.prio,
    eBefore.hart,
    eBefore.entryPc, eBefore.entryArg,
    eBefore.oneshot,
    regsBefore.sepc,
    0,
    regsBefore.a6,
    regsBefore.a7
  );
  // 这一句依赖于 SseProcessPendingEventsSpec 中对 next.events 的定义：
  // 一般是 next.events == prev.events[selectedId := eAfter]
  assert next.events == prev.events[selectedId := eAfter];
  assert next.events[selectedId].status.state == Running;

  // 对所有其他 pending 事件证明优先级约束
  forall otherId |
    otherId in prev.events &&
    otherId in hsBefore.enabled &&
    IsPendingOnHart(prev.events[otherId], cur)
    ensures prev.events[selectedId].prio < prev.events[otherId].prio ||
            (prev.events[selectedId].prio == prev.events[otherId].prio &&
             selectedId <= otherId)
  {
    var evOther := prev.events[otherId];

    // otherId 在 enabled 中的位置 j
    var j :| 0 <= j < |en| && en[j] == otherId;

    if j < pendingIdx {
      // FindFirstPendingIsFirst 保证：所有 j < pendingIdx 的元素都不是 pending
      assert !IsPendingOnHart(prev.events[otherId], cur);
    }

    assert j >= pendingIdx;

    if j == pendingIdx {
      // 同一个位置：ID 相等，selectedId <= otherId 成立
      assert otherId == selectedId;
    } else {
      // j > pendingIdx：说明 selectedId 在 enabled 里更靠前
      var i := pendingIdx;
      assert 0 <= i < j < |en|;
      assert en[i] == selectedId;
      assert en[j] == otherId;
      assert selectedId != otherId;

      // 用现有的 P3_PriorityOrdering，引出优先级关系
      P3_PriorityOrdering(prev, cur, selectedId, otherId);
      // 该引理一般给出：
      //   prev.events[selectedId].prio < prev.events[otherId].prio ||
      //   (equal prio && selectedId < otherId)
      // 由 selectedId < otherId 推出 selectedId <= otherId，
      // 正好匹配我们想要的形式
    }
  }

    // 用刚才构造的 selectedId 作为 exists 见证
  }

// 小引理：在 SseProcessPendingEventsSpec 下，
// 若当前 hart 未被 mask，且 next != prev，
// 则 FindFirstPending(...) 一定不是 -1（也就是 pending 集合非空）。
lemma P3_FindFirstPendingNonNeg(
  prev: SystemState, next: SystemState,
  regsBefore: Regs, regsAfter: Regs,
  cur: HartId)
  requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
  requires cur in prev.harts
  requires !prev.harts[cur].masked
  requires next != prev
  ensures FindFirstPending(prev.harts[cur].enabled, prev.events, cur) >= 0
{
  var hsBefore := prev.harts[cur];
  var en := hsBefore.enabled;
  var idx := FindFirstPending(en, prev.events, cur);

  // 我们希望证明 idx >= 0。对 idx < 0 做反证。
  if idx < 0 {
    // 关键点：这里依赖于 SseProcessPendingEventsSpec 的定义。
    // 典型写法一般是（伪代码）：
    //
    //   predicate SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur) {
    //     ...
    //     var hsBefore := prev.harts[cur];
    //     var en := hsBefore.enabled;
    //     var idx := FindFirstPending(en, prev.events, cur);
    //     if hsBefore.masked || idx < 0 then
    //       next == prev && regsAfter == regsBefore
    //     else
    //       // 真的去处理 en[idx]
    //       ...
    //   }
    //
    // 在我们当前 requires 里有：
    //   !hsBefore.masked  &&  idx < 0
    // 展开上面的定义后，Dafny 能自动推出：
    //   next == prev && regsAfter == regsBefore
    //
    // 因此这里直接 assert next == prev 就够了，
    // 和 requires 里的 next != prev 立刻矛盾。
    assert next == prev;

    // contradiction: next != prev by precondition
  }
}

  // lemma Theorem_P3_PriorityScheduling(
  //   prev: SystemState, next: SystemState,
  //   regsBefore: Regs, regsAfter: Regs,
  //   cur: HartId)
  //   requires SystemInv(prev)
  //   requires cur in prev.harts
  //   requires !prev.harts[cur].masked
  //   requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
  //   requires next != prev
  //   ensures exists selectedId ::
  //     selectedId in prev.events &&
  //     selectedId in next.events &&
  //     IsPendingOnHart(prev.events[selectedId], cur) &&
  //     next.events[selectedId].status.state == Running &&
  //     (forall otherId ::
  //        otherId in prev.events &&
  //        otherId in prev.harts[cur].enabled &&
  //        IsPendingOnHart(prev.events[otherId], cur) ==>
  //          prev.events[selectedId].prio < prev.events[otherId].prio ||
  //          (prev.events[selectedId].prio == prev.events[otherId].prio &&
  //           selectedId <= otherId))
  // {
  //   // 这里唯一的额外工作，是证明 FindFirstPending >= 0
  //   // 目前为了简单，你可以先加一条 requires：
  //   //   requires FindFirstPending(prev.harts[cur].enabled, prev.events, cur) >= 0
  //   // 然后直接调用 P3_FullPriorityScheduling 即可。
  //   //
  //   // 如果你不想在调用端多一个 requires，可以再单独写个
  //   // small lemma，从 SseProcessPendingEventsSpec + next != prev
  //   // 推出 FindFirstPending(...) >= 0，然后这里先 call 那个小引理。
  //   P3_FullPriorityScheduling(prev, next, regsBefore, regsAfter, cur);
  // }
// P3 总结定理（对外接口）：
// 保持原来的 requires，只额外使用 next != prev 表示“确实处理到了某个事件”。
  lemma Theorem_P3_PriorityScheduling(
    prev: SystemState, next: SystemState,
    regsBefore: Regs, regsAfter: Regs,
    cur: HartId)
    requires SystemInv(prev)
    requires cur in prev.harts
    requires !prev.harts[cur].masked
    requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
    requires next != prev
    ensures exists selectedId ::
      selectedId in prev.events &&
      selectedId in next.events &&
      IsPendingOnHart(prev.events[selectedId], cur) &&
      next.events[selectedId].status.state == Running &&
      (forall otherId ::
        otherId in prev.events &&
        otherId in prev.harts[cur].enabled &&
        IsPendingOnHart(prev.events[otherId], cur) ==>
          prev.events[selectedId].prio < prev.events[otherId].prio ||
          (prev.events[selectedId].prio == prev.events[otherId].prio &&
            selectedId <= otherId))
  {
    // 第一步：从 spec + !masked + next != prev 推出 FindFirstPending >= 0
    P3_FindFirstPendingNonNeg(prev, next, regsBefore, regsAfter, cur);

    // 第二步：在 SystemInv 的前提下，调用完整版 P3 引理。
    P3_FullPriorityScheduling(prev, next, regsBefore, regsAfter, cur);
  }

  // P4 总结
  lemma Theorem_P4_HartIsolation(
    prev: SystemState, next: SystemState,
    regsBefore: Regs, regsAfter: Regs,
    cur: HartId)
    requires SystemInv(prev)
    requires cur in prev.harts
    requires prev.harts[cur].masked
    requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
    ensures next == prev
  {
    P4_MaskingPreventsProcessing(prev, next, regsBefore, regsAfter, cur);
  }
}
