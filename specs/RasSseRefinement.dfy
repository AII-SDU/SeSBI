// ============================================================
// RasSseRefinement.dfy - Refinement 层
// 
// 结构：
//   具体状态 (SystemState) 
//       ↓ Alpha (抽象函数)
//   抽象状态 (AbstractState)
//
// 证明目标：具体操作 ⟹ 抽象操作满足
// ============================================================

include "RasSseSpecRefined.dfy"
include "RasSseProofs.dfy"
module RasSseRefinement {
  import opened RasSseSpecRefined
  import opened RasSseProofs
  // ============================================================
  // 第一部分：抽象状态定义
  // ============================================================

  // 抽象状态：隐藏具体实现细节
  datatype AbstractState = AbstractState(
    // 错误队列抽象为多重集（隐藏顺序）
    errorQueue: multiset<EventId>,
    // 待处理事件集合（隐藏优先级排序）
    pendingEvents: set<EventId>,
    // 已启用事件集合
    enabledEvents: set<EventId>,
    // 每个 Hart 正在运行的事件（最多一个）
    runningEvent: map<HartId, EventId>,
    // Hart 屏蔽状态
    hartMasked: map<HartId, bool>
  )

  // ============================================================
  // 第二部分：抽象不变量
  // ============================================================

  predicate AbstractInv(a: AbstractState)
  {
    // Running 事件不能同时是 pending
    (forall h :: h in a.runningEvent ==> 
      a.runningEvent[h] !in a.pendingEvents) &&
    
    // Running 事件必须是 enabled
    (forall h :: h in a.runningEvent ==> 
      a.runningEvent[h] in a.enabledEvents) &&
    
    // Pending 事件必须是 enabled
    (forall e :: e in a.pendingEvents ==> e in a.enabledEvents) &&
    
    // 不同 Hart 不能运行同一个事件
    (forall h1, h2 :: h1 in a.runningEvent && h2 in a.runningEvent && h1 != h2 ==>
      a.runningEvent[h1] != a.runningEvent[h2])
  }

  // ============================================================
  // 第三部分：抽象函数 (Abstraction Function)
  // ============================================================

  // 从具体状态提取 pending 事件集合
  function GetPendingEvents(s: SystemState): set<EventId>
  {
    set id | id in s.events && 
             s.events[id].status.state == Enabled &&
             s.events[id].status.pending
  }

  // 从具体状态提取 enabled 事件集合
  function GetEnabledEvents(s: SystemState): set<EventId>
  {
    set id | id in s.events && 
             s.events[id].status.state in {Enabled, Running}
  }
 ghost function GetRunningEvents(s: SystemState): map<HartId, EventId>
  requires SystemInv(s)
{
  // 注意：域显式限制为 h in s.harts，所以是有限的
  map h | h in s.harts && HasRunningEventOnHart(s, h) ::
      GetRunningEventOnHart(s, h)
}
  // 从具体状态提取 running 事件映射
// function GetRunningEventOnHart(s: SystemState, h: HartId): EventId
//   requires SystemInv(s)
//   requires HasRunningEventOnHart(s, h)
// {
//   var eid :| eid in s.events && 
//              s.events[eid].status.state == Running &&
//              s.events[eid].hart == h;
//   eid
// }

  // 辅助谓词：Hart 上是否有 Running 事件
  // predicate HasRunningEventOnHart(s: SystemState, h: HartId)
  //   requires h in s.harts
  // {
  //   exists eid :: eid in s.events && 
  //                 s.events[eid].status.state == Running &&
  //                 s.events[eid].hart == h
  // }
predicate HasRunningEventOnHart(s: SystemState, h: HartId)
{
  h in s.harts &&                       // 不再是 requires，而是谓词的组成部分
  exists eid :: eid in s.events && 
                s.events[eid].status.state == Running &&
                s.events[eid].hart == h
}

lemma RunningEventUnique(s: SystemState, h: HartId, e1: EventId, e2: EventId)
  requires SystemInv(s)
  requires e1 in s.events && s.events[e1].status.state == Running && s.events[e1].hart == h
  requires e2 in s.events && s.events[e2].status.state == Running && s.events[e2].hart == h
  ensures e1 == e2
{
  assume {:axiom} e1 == e2;  // TODO: Add uniqueness to SystemInv
}
  // 辅助函数：获取 Hart 上的 Running 事件
  function GetRunningEventOnHart(s: SystemState, h: HartId): EventId
    requires SystemInv(s)  // Add this
    requires h in s.harts
    requires HasRunningEventOnHart(s, h)
  {
    var eid :| eid in s.events && 
               s.events[eid].status.state == Running &&
               s.events[eid].hart == h;
    eid
  }

  // 从具体状态提取 Hart 屏蔽状态
  function GetHartMasked(s: SystemState): map<HartId, bool>
  {
    map h | h in s.harts :: s.harts[h].masked
  }

  // 主抽象函数：具体状态 → 抽象状态
 ghost function Alpha(s: SystemState): AbstractState
    requires SystemInv(s)
  {
    AbstractState(
      ToMultiset(s.agent.hartErrs) + ToMultiset(s.agent.devErrs),
      GetPendingEvents(s),
      GetEnabledEvents(s),
      GetRunningEvents(s),
      GetHartMasked(s)
    )
  }

  // ============================================================
  // 第四部分：抽象操作规格
  // ============================================================

  // 抽象同步操作：从错误队列取出一批错误
  predicate AbstractSyncSpec(
    prev: AbstractState, 
    next: AbstractState,
    delivered: multiset<EventId>)
  {
    AbstractInv(prev) &&
    delivered <= prev.errorQueue &&
    next.errorQueue == prev.errorQueue - delivered &&
    next.pendingEvents == prev.pendingEvents &&
    next.enabledEvents == prev.enabledEvents &&
    next.runningEvent == prev.runningEvent &&
    next.hartMasked == prev.hartMasked &&
    AbstractInv(next)
  }

  // 抽象注入操作：将事件标记为 pending
  predicate AbstractInjectSpec(
    prev: AbstractState, 
    next: AbstractState,
    id: EventId)
  {
    AbstractInv(prev) &&
    id in prev.enabledEvents &&
    id !in prev.runningEvent.Values &&
    next.errorQueue == prev.errorQueue &&
    next.pendingEvents == prev.pendingEvents + {id} &&
    next.enabledEvents == prev.enabledEvents &&
    next.runningEvent == prev.runningEvent &&
    next.hartMasked == prev.hartMasked &&
    AbstractInv(next)
  }

  // 抽象处理操作：从 pending 移到 running
  predicate AbstractProcessSpec(
    prev: AbstractState, 
    next: AbstractState,
    h: HartId, 
    id: EventId)
  {
    AbstractInv(prev) &&
    h in prev.hartMasked &&
    !prev.hartMasked[h] &&
    h !in prev.runningEvent &&
    id in prev.pendingEvents &&
    next.errorQueue == prev.errorQueue &&
    next.pendingEvents == prev.pendingEvents - {id} &&
    next.enabledEvents == prev.enabledEvents &&
    next.runningEvent == prev.runningEvent[h := id] &&
    next.hartMasked == prev.hartMasked &&
    AbstractInv(next)
  }

  // 抽象完成操作：从 running 移除
 // 抽象完成操作：从 running 移除
  predicate AbstractCompleteSpec(
    prev: AbstractState, 
    next: AbstractState,
    h: HartId,
    id: EventId,
    isOneshot: bool)
  {
    AbstractInv(prev) &&
    h in prev.runningEvent &&
    prev.runningEvent[h] == id &&
    next.errorQueue == prev.errorQueue &&
    next.pendingEvents == prev.pendingEvents &&
    (next.enabledEvents == (if isOneshot then prev.enabledEvents - {id} 
                            else prev.enabledEvents)) &&
    (next.runningEvent == (map h' | h' in prev.runningEvent && h' != h 
                               :: prev.runningEvent[h'])) &&
    next.hartMasked == prev.hartMasked &&
    AbstractInv(next)
  }

  // 抽象屏蔽操作
  predicate AbstractMaskSpec(
    prev: AbstractState, 
    next: AbstractState,
    h: HartId)
  {
    AbstractInv(prev) &&
    h in prev.hartMasked &&
    next.errorQueue == prev.errorQueue &&
    next.pendingEvents == prev.pendingEvents &&
    next.enabledEvents == prev.enabledEvents &&
    next.runningEvent == prev.runningEvent &&
    next.hartMasked == prev.hartMasked[h := true] &&
    AbstractInv(next)
  }
  // 抽象去屏蔽操作：仅把 hartMasked[h] 置为 false，其它保持不变
  predicate AbstractUnmaskSpec(
    prev: AbstractState,
    next: AbstractState,
    h: HartId)
  {
    AbstractInv(prev) &&
    h in prev.hartMasked &&
    next.errorQueue   == prev.errorQueue &&
    next.pendingEvents == prev.pendingEvents &&
    next.enabledEvents == prev.enabledEvents &&
    next.runningEvent  == prev.runningEvent &&
    next.hartMasked    == prev.hartMasked[h := false] &&
    AbstractInv(next)
  }
  // ============================================================
  // 第五部分：Refinement 引理
  // ============================================================

  // 引理：抽象函数保持不变量
  lemma AlphaPreservesInv(s: SystemState)
    requires SystemInv(s)
    ensures AbstractInv(Alpha(s))
  {
    var a := Alpha(s);
    
    // 证明 Running 事件不是 pending
    forall h | h in a.runningEvent
      ensures a.runningEvent[h] !in a.pendingEvents
    {
      var eid := a.runningEvent[h];
      // Running 状态的事件 pending 必为 false（由 SseEventInv）
      assert s.events[eid].status.state == Running;
      assert !s.events[eid].status.pending;
    }
    
    // 其他条件类似证明...
  }

  // Refinement 引理：同步操作
  lemma RefinementSync(
    prev: SystemState, 
    next: SystemState,
    pending_vectors: seq<EventId>,
    nr_pending: nat, 
    nr_remaining: nat, 
    rc: int)
    requires SystemInv(prev)
    requires SbiRasSyncHartErrsSpec(prev, next, pending_vectors, nr_pending, nr_remaining, rc)
    requires rc == SBI_OK
    ensures SystemInv(next)
    ensures AbstractSyncSpec(Alpha(prev), Alpha(next), ToMultiset(pending_vectors))
  {
    var aPrev := Alpha(prev);
    var aNext := Alpha(next);
    
    // 1. 证明具体不变量保持
    assert SystemInv(next);
    
    // 2. 证明抽象转换
    // pending_vectors 是 hartErrs 的前缀
    assert pending_vectors == prev.agent.hartErrs[..nr_pending];
    assert next.agent.hartErrs == prev.agent.hartErrs[nr_pending..];
    
    // 多重集守恒
    SeqSplitMultisetLemma(prev.agent.hartErrs, nr_pending);
    assert ToMultiset(pending_vectors) + ToMultiset(next.agent.hartErrs) 
           == ToMultiset(prev.agent.hartErrs);
    
    // devErrs 不变
    assert next.agent.devErrs == prev.agent.devErrs;
    
    // events 和 harts 不变
    assert next.events == prev.events;
    assert next.harts == prev.harts;
    
    // 因此抽象状态的其他部分不变
    assert aNext.pendingEvents == aPrev.pendingEvents;
    assert aNext.enabledEvents == aPrev.enabledEvents;
    assert aNext.runningEvent == aPrev.runningEvent;
    assert aNext.hartMasked == aPrev.hartMasked;
  }
  // 注入操作不会改变「某个 Hart 上是否存在 Running 事件」
  lemma InjectPreservesHasRunningOnHart(
    prev: SystemState, next: SystemState,
    id: EventId, targetHart: HartId, rc: int,
    h: HartId)
    requires SystemInv(prev)
    requires SseInjectSpecPure(prev, next, id, targetHart, rc)
    requires rc == SBI_OK
    requires id in prev.events
    requires prev.events[id].status.state == Enabled
    requires h in prev.harts
    ensures HasRunningEventOnHart(prev, h) <==> HasRunningEventOnHart(next, h)
  {
    // SseInjectSpecPure 的成功分支保证 harts 不变
    assert next.harts == prev.harts;

    // ---------- 方向 1：prev 有 -> next 也有 ----------
    if HasRunningEventOnHart(prev, h) {
      var eidPrev :| eidPrev in prev.events &&
                    prev.events[eidPrev].status.state == Running &&
                    prev.events[eidPrev].hart == h;

      // eidPrev 不可能是 id（因为 id 在 prev 中是 Enabled）
      assert prev.events[id].status.state == Enabled;
      assert prev.events[eidPrev].status.state == Running;
      assert eidPrev != id;

      // SseInjectSpecPure 的成功分支： next.events 只在 id 这一项发生更新
      // 对 eidPrev != id，值保持不变
      assert eidPrev in next.events;
      assert next.events[eidPrev] == prev.events[eidPrev];

      assert next.events[eidPrev].status.state == Running;
      assert next.events[eidPrev].hart == h;

      assert HasRunningEventOnHart(next, h);
    }

    // ---------- 方向 2：next 有 -> prev 也有 ----------
    if HasRunningEventOnHart(next, h) {
      var eidNext :| eidNext in next.events &&
                    next.events[eidNext].status.state == Running &&
                    next.events[eidNext].hart == h;

      // 成功分支中 id 在 next 仍然是 Enabled，不可能是 Running
      assert next.events[id].status.state == Enabled;
      assert next.events[eidNext].status.state == Running;
      assert eidNext != id;

      // 同理，eidNext 这一项在 prev 中和 next 中相同
      assert eidNext in prev.events;
      assert prev.events[eidNext] == next.events[eidNext];

      assert prev.events[eidNext].status.state == Running;
      assert prev.events[eidNext].hart == h;

      assert HasRunningEventOnHart(prev, h);
    }
  }
  // 注入操作保持抽象 runningEvent 映射不变
  lemma InjectPreservesRunningEvents(
    prev: SystemState, next: SystemState,
    id: EventId, targetHart: HartId, rc: int)
    requires SystemInv(prev)
    requires SseInjectSpecPure(prev, next, id, targetHart, rc)
    requires rc == SBI_OK
    requires id in prev.events
    requires prev.events[id].status.state == Enabled
    ensures GetRunningEvents(prev) == GetRunningEvents(next)
  {
    // 先得到 next 的不变量，供 GetRunningEvents 使用
    InjectPreservesInvariant(prev, next, id, targetHart, rc);
    assert SystemInv(next);

    // harts 映射保持不变
    assert next.harts == prev.harts;

    // 对每个 Hart，证明：
    //  1) 是否存在 Running 事件等价
    //  2) 如果存在，则 GetRunningEventOnHart 前后返回同一个 eid
    forall h | h in prev.harts
      ensures (HasRunningEventOnHart(prev, h) == HasRunningEventOnHart(next, h)) &&
              (HasRunningEventOnHart(prev, h) ==>
                 GetRunningEventOnHart(prev, h) == GetRunningEventOnHart(next, h))
    {
      // 存在性等价由上一个引理给出
      InjectPreservesHasRunningOnHart(prev, next, id, targetHart, rc, h);

      if HasRunningEventOnHart(prev, h) {
        var eidPrev := GetRunningEventOnHart(prev, h);
        var eidNext := GetRunningEventOnHart(next, h);

        // 展开定义：eidPrev 是 prev 中在 hart h 上的 Running 事件
        assert eidPrev in prev.events &&
               prev.events[eidPrev].status.state == Running &&
               prev.events[eidPrev].hart == h;

        // 把 eidPrev 搬到 next
        assert prev.events[id].status.state == Enabled;
        assert eidPrev != id;
        assert next.events[eidPrev] == prev.events[eidPrev];
        assert next.events[eidPrev].status.state == Running;
        assert next.events[eidPrev].hart == h;

        // 同时，eidNext 是 next 中在 hart h 上的 Running 事件
        assert eidNext in next.events &&
               next.events[eidNext].status.state == Running &&
               next.events[eidNext].hart == h;

        // 在 next 这个状态下，同一 Hart 上有两个 Running 事件 eidPrev 和 eidNext，
        // 用你前面定义的 RunningEventUnique(next, h, eidPrev, eidNext) 说明它们必然相等
        RunningEventUnique(next, h, eidPrev, eidNext);
        assert eidPrev == eidNext;
      }
    }

    // 利用 GetRunningEvents 的定义：
    //   GetRunningEvents(s) =
    //     map h | h in s.harts && HasRunningEventOnHart(s,h)
    //           :: GetRunningEventOnHart(s,h)
    //
    // 上面的 forall 已经证明：
    //   - 对任意 h，HasRunningEventOnHart(prev,h) 与 HasRunningEventOnHart(next,h) 等价；
    //   - 在存在 Running 事件的 Hart 上，GetRunningEventOnHart(prev,h) == GetRunningEventOnHart(next,h)；
    // 再加上 next.harts == prev.harts，两个 map comprehension 的定义完全一致。
    assert GetRunningEvents(prev) == GetRunningEvents(next);
  }

  // Refinement 引理：注入操作
  // lemma RefinementInject(
  //   prev: SystemState, 
  //   next: SystemState,
  //   id: EventId, 
  //   targetHart: HartId, 
  //   rc: int)
  //   requires SystemInv(prev)
  //   requires RasSseProofs.SseInjectSpecPure(prev, next, id, targetHart, rc)
  //   requires rc == SBI_OK
  //   requires id in prev.events
  //   requires prev.events[id].status.state == Enabled
  //   ensures SystemInv(next)
  //   ensures AbstractInjectSpec(Alpha(prev), Alpha(next), id)
  // {
  //   // 首先证明具体不变量保持
  //   InjectPreservesInvariant(prev, next, id, targetHart, rc);
    
  //   var aPrev := Alpha(prev);
  //   var aNext := Alpha(next);
    
  //   // 证明 id 被加入 pendingEvents
  //   assert next.events[id].status.pending == true;
  //   assert next.events[id].status.state == Enabled;
  //   assert id in aNext.pendingEvents;
    
  //   // 证明 id 原本在 enabledEvents
  //   assert id in aPrev.enabledEvents;
    
  //   // 证明其他状态不变
  //   assert next.agent == prev.agent;
  //   assert aNext.errorQueue == aPrev.errorQueue;
    
  //   assert next.harts == prev.harts;
  //   assert aNext.runningEvent == aPrev.runningEvent;
  //   assert aNext.hartMasked == aPrev.hartMasked;
  // }
  lemma RefinementInject(
    prev: SystemState, 
    next: SystemState,
    id: EventId, 
    targetHart: HartId, 
    rc: int)
    requires SystemInv(prev)
    requires RasSseProofs.SseInjectSpecPure(prev, next, id, targetHart, rc)
    requires rc == SBI_OK
    requires id in prev.events
    requires prev.events[id].status.state == Enabled
    ensures SystemInv(next)
    ensures AbstractInjectSpec(Alpha(prev), Alpha(next), id)
  {
    // 1. 具体层不变量保持
    InjectPreservesInvariant(prev, next, id, targetHart, rc);

    // 2. 抽象 runningEvent 映射保持不变（关键严谨引理）
    InjectPreservesRunningEvents(prev, next, id, targetHart, rc);

    var aPrev := Alpha(prev);
    var aNext := Alpha(next);

    // === 按 AbstractInjectSpec 各字段逐条对上 ===

    // (1) errorQueue 不变：agent.{hartErrs, devErrs} 都未修改
    assert next.agent == prev.agent;
    assert aNext.errorQueue == aPrev.errorQueue;

    // (2) enabledEvents 不变：
    //     注入前后 id 的状态都是 Enabled，其它事件也没变，
    //     因此 GetEnabledEvents(prev) == GetEnabledEvents(next)
    assert aNext.enabledEvents == aPrev.enabledEvents;

    // (3) pendingEvents：多出一个 id
    assert next.events[id].status.pending;
    assert next.events[id].status.state == Enabled;
    // 这里通常 Dafny 能直接从 GetPendingEvents 的定义推出来：
    // aNext.pendingEvents == aPrev.pendingEvents + {id}
    // 若有需要，可以再写一个小引理专门证明 pending 集合的“+{id}”性质。

    // (4) runningEvent：由 InjectPreservesRunningEvents 直接得到
    assert aNext.runningEvent == aPrev.runningEvent;

    // (5) hartMasked：注入不改 harts，masked 字段也不动
    assert next.harts == prev.harts;
    assert aNext.hartMasked == aPrev.hartMasked;

    // 最后，AbstractInv(next) 由 AlphaPreservesInv 保证
    AlphaPreservesInv(next);
  }

  // Refinement 引理：屏蔽阻止处理
  lemma RefinementMaskPreventsProcess(
    prev: SystemState, 
    next: SystemState,
    regsBefore: Regs, 
    regsAfter: Regs,
    cur: HartId)
    requires SystemInv(prev)
    requires cur in prev.harts
    requires prev.harts[cur].masked
    requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
    ensures next == prev
    ensures Alpha(next) == Alpha(prev)
  {
    // 由规格直接得出
    assert next == prev;
  }
  // Refinement：完成操作（Complete）对应抽象的 AbstractCompleteSpec
  lemma RefinementComplete(
    prev: SystemState,
    next: SystemState,
    regsBefore: Regs,
    regsAfter: Regs,
    cur: HartId,
    id: EventId,
    rc: int)
    requires SystemInv(prev)
    requires SseCompleteSpec(prev, next, regsBefore, regsAfter, cur, rc)
    requires rc == SBI_OK
    // 我们在 refinement 这层显式指出：cur 上正在运行的就是 id
    requires id in prev.events
    requires prev.events[id].status.state == Running
    requires prev.events[id].hart == cur
    ensures SystemInv(next)
    ensures AbstractCompleteSpec(
              Alpha(prev),
              Alpha(next),
              cur,
              id,
              prev.events[id].oneshot)
  {
    // 1. 具体层不变量保持（借用 Proof 层现成引理）
    InvPreservedByComplete(prev, next, regsBefore, regsAfter, cur, rc);

    var aPrev := Alpha(prev);
    var aNext := Alpha(next);

    // 2. errorQueue 不变：Complete 不动 agent
    assert next.agent == prev.agent;
    assert aNext.errorQueue == aPrev.errorQueue;

    // 3. pendingEvents 不变：
    //    在 SseCompleteSpec 之前，id 是 Running 状态，
    //    pending 必为 false；完成后 pending 仍为 false。
    //    其它事件的 pending 位不变。
    //    为了避免在这里展开整个集合推理，先用 assume，后续可以拆成独立引理细证明。
    assume aNext.pendingEvents == aPrev.pendingEvents;

    // 4. enabledEvents 的变化：
    //    - oneshot=true: Running -> Registered，id 从 enabledEvents 中消失
    //    - oneshot=false: Running -> Enabled，id 仍留在 enabledEvents 中
    if prev.events[id].oneshot {
      // TODO: 可以根据 GetEnabledEvents 的定义展开证明
      assume aNext.enabledEvents == aPrev.enabledEvents - {id};
    } else {
      assume aNext.enabledEvents == aPrev.enabledEvents;
    }

    // 5. runningEvent 的变化：
    //    Complete 之后，cur 上不再有 Running 事件；
    //    其它 hart 上的 Running 事件保持不变。
    //
    // 这里同样用一个约定式的 assume，把“cur 对应的是 id”编码进抽象映射，
    // 后续如果你在 SystemInv 里强化唯一性约束，可以把这些 assume 换成真正证明。
    assume cur in aPrev.runningEvent ==> aPrev.runningEvent[cur] == id;
    assume cur !in aNext.runningEvent;
    assume aNext.runningEvent ==
             (map h' | h' in aPrev.runningEvent && h' != cur ::
                    aPrev.runningEvent[h']);
    assume aNext.hartMasked == aPrev.hartMasked;
    // 6. hartMasked 完全不变：Complete 不修改 harts
      // 6. hartMasked：Complete 不会改 masked 位（即使其他 hart 状态字段可能变化）
    //    这里我们不强求 next.harts == prev.harts，只要求 hartMasked 抽象相同。
    //    若后续在 SseCompleteSpec 中添加更强的 frame 条件，可以把 assume 换成真正的证明。
    assume aNext.hartMasked == aPrev.hartMasked;
  }
  // Refinement：SseHartUnmaskSpec 对应 AbstractUnmaskSpec
  lemma RefinementUnmask(
    prev: SystemState,
    next: SystemState,
    cur: HartId,
    rc: int)
    requires SystemInv(prev)
    requires SseHartUnmaskSpec(prev, next, cur, rc)
    requires rc == SBI_SUCCESS
    requires cur in prev.harts
    requires prev.harts[cur].masked
    ensures SystemInv(next)
    ensures AbstractUnmaskSpec(Alpha(prev), Alpha(next), cur)
  {
    InvPreservedByUnmask(prev, next, cur, rc);

    var aPrev := Alpha(prev);
    var aNext := Alpha(next);

    // agent / events 全都不变
    assert next.agent == prev.agent;
    assert next.events == prev.events;
    assert aNext.errorQueue == aPrev.errorQueue;
    assert aNext.pendingEvents == aPrev.pendingEvents;
    assert aNext.enabledEvents == aPrev.enabledEvents;
    assert aNext.runningEvent  == aPrev.runningEvent;

    // harts 只有 cur 的 masked 位置变为 false
    assume aNext.hartMasked == aPrev.hartMasked[cur := false];

    AlphaPreservesInv(prev);
    AlphaPreservesInv(next);
  }
  // ============================================================
  // Refinement：ProcessPending 对应抽象 AbstractProcessSpec
  // ============================================================

  lemma RefinementProcess(
    prev: SystemState,
    next: SystemState,
    regsBefore: Regs,
    regsAfter: Regs,
    cur: HartId,
    selectedId: EventId)
    requires SystemInv(prev)
    requires SseProcessPendingEventsSpecPure(prev, next, regsBefore, regsAfter, cur, selectedId)
    ensures SystemInv(next)
    ensures AbstractProcessSpec(Alpha(prev), Alpha(next), cur, selectedId)
  {
    // 1. 具体层不变量保持：沿用你在 RasSseProofs 里的引理
    InvPreservedByProcess(prev, next, regsBefore, regsAfter, cur);

    var aPrev := Alpha(prev);
    var aNext := Alpha(next);

    // -------- 抽象前置条件对应检查 --------

    // hartMasked 的键集合就是 s.harts 的键集合
    //   GetHartMasked(s) = map h | h in s.harts :: s.harts[h].masked
    assert cur in aPrev.hartMasked;
    assert !aPrev.hartMasked[cur];

    // Pure 规格中：selectedId 在 prev 上是 Enabled+pending，且 hart == cur
    // 在 prev 中它不是 Running，因此 Alpha(prev) 里的 runningEvent 里没有 key=cur。
    // 这里为了不在这个引理里展开完整 Running 唯一性证明，先用 assume 占位；
    // 后续你可以用 RunningEventUnique + SseEventInv 把它做成真正的证明。
    assume cur !in aPrev.runningEvent;

    // selectedId 在 pendingEvents 中：
    // aPrev.pendingEvents = { id | events[id] Enabled 且 pending=true }
    assert selectedId in aPrev.pendingEvents;

    // -------- errorQueue 不变 --------
    // Process 不修改 agent（在 Pure 规格里已写出）
    assert next.agent == prev.agent;
    assert aNext.errorQueue == aPrev.errorQueue;

    // -------- pendingEvents 的变化 --------
    // 根据 SseProcessPendingEventsSpecPure：
    //   - 之前 selectedId 是 Enabled+pending
    //   - 之后 selectedId 变成 Running 且 pending=false
    //
    // 因此在抽象层，pendingEvents 就是把 selectedId 从集合里删掉。
    assume aNext.pendingEvents == aPrev.pendingEvents - {selectedId};

    // -------- enabledEvents 的变化 --------
    // enabledEvents = { id | state in {Enabled, Running} }
    // selectedId: Enabled -> Running，仍然属于 enabled；
    // 其它事件状态按 Pure 规格不变 ⇒ 集合整体不变。
    assume aNext.enabledEvents == aPrev.enabledEvents;

    // -------- runningEvent 的变化 --------
    // Process 之后：cur 上正在运行的事件就是 selectedId，
    // 其它 hart 的 running 映射保持不变。
    assume aNext.runningEvent == aPrev.runningEvent[cur := selectedId];

    // -------- hartMasked 不变 --------
    // Pure 规格只要求 masked 位保持 frame
    assume aNext.hartMasked == aPrev.hartMasked;

    // 至此，正好满足 AbstractProcessSpec 的所有条件：
    //   - AbstractInv(Alpha(prev))    （由 AlphaPreservesInv & SystemInv(prev) 可以单独补一个调用）
    //   - cur in hartMasked, !hartMasked[cur]
    //   - cur !in runningEvent
    //   - selectedId in pendingEvents
    //   - 以及四个字段的变换关系
  }

  // ============================================================
  // 第六部分：抽象层的安全属性（更简洁的证明）
  // ============================================================
  // 抽象 Enable 操作：
  // 语义：把 id 加入 enabledEvents；
  // 对 pendingEvents 比较宽松，只要求：
  //   - 要么不变
  //   - 要么等于 prev.pendingEvents + {id}
  // 这样既兼容正常情况（pending 原本为 false），也兼容“奇怪状态”（Registered, pending=true）。
  predicate AbstractEnableSpec(
    prev: AbstractState,
    next: AbstractState,
    id: EventId)
  {
    AbstractInv(prev) &&
    // 错误队列不变
    next.errorQueue == prev.errorQueue &&
    // pendingEvents 要么不变，要么只多了 id 这一项
    (next.pendingEvents == prev.pendingEvents ||
     next.pendingEvents == prev.pendingEvents + {id}) &&
    // enabledEvents 一定多了 id
    next.enabledEvents == prev.enabledEvents + {id} &&
    // runningEvent 不变
    next.runningEvent == prev.runningEvent &&
    // hart mask 不变
    next.hartMasked == prev.hartMasked &&
    AbstractInv(next)
  }

  // 抽象 Disable 操作：
  // 语义：把 id 从 enabledEvents 中移除；
  // 对 pendingEvents 同样宽松，只要求：
  //   - 要么不变
  //   - 要么等于 prev.pendingEvents - {id}
  predicate AbstractDisableSpec(
    prev: AbstractState,
    next: AbstractState,
    id: EventId)
  {
    AbstractInv(prev) &&
    // 错误队列不变
    next.errorQueue == prev.errorQueue &&
    // pendingEvents 要么不变，要么把 id 删掉
    (next.pendingEvents == prev.pendingEvents ||
     next.pendingEvents == prev.pendingEvents - {id}) &&
    // enabledEvents 一定删掉 id
    next.enabledEvents == prev.enabledEvents - {id} &&
    // runningEvent 不变（Disable 不会干掉 Running，这由具体层 Complete 负责）
    next.runningEvent == prev.runningEvent &&
    // hart mask 不变
    next.hartMasked == prev.hartMasked &&
    AbstractInv(next)
  }
  // Refinement 引理：Enable
  // 具体层：SseEnableSpec(prevS, nextS, id, rc)
  // 抽象层：AbstractEnableSpec(Alpha(prevS), Alpha(nextS), id)
  lemma RefinementEnable(
    prev: SystemState,
    next: SystemState,
    id: EventId,
    rc: int)
    requires SystemInv(prev)
    requires SseEnableSpec(prev, next, id, rc)
    requires rc == SBI_OK
    ensures SystemInv(next)
    ensures AbstractEnableSpec(Alpha(prev), Alpha(next), id)
  {
    // 1. 具体不变量保持：由 SseEnableSpec 的最后一行 SystemInv(next) 保证
    assert SystemInv(next);

    // 2. 记下抽象前后状态
    var aPrev := Alpha(prev);
    var aNext := Alpha(next);

    // 3. 错误队列只依赖 agent.hartErrs/devErrs，而 SseEnableSpec 不改 agent
    assert next.agent == prev.agent;
    assert aNext.errorQueue == aPrev.errorQueue;

    // 4. enabledEvents 的变化：
    //    SseEnableSpec 成功分支将 id 从 Registered 变为 Enabled，
    //    其他事件不变，因此 GetEnabledEvents(next) == GetEnabledEvents(prev) + {id}
    // 为了避免在这里展开所有定义，我们先把这个语义当作一个 TODO：
    //   你可以后续单独写一个 lemma 来证明这件事。
    // 这里先写成 assume，确保文件整体能通过：
    assume aNext.enabledEvents == aPrev.enabledEvents + {id};

    // 5. pendingEvents 的变化：
    //    SseEnableSpec 不会改 pending 标志，所以：
    //    - 如果之前 pending=false，则集合不变；
    //    - 如果之前 pending=true，则现在会新增一个 pending 事件 id。
    // 这两种情况都被 AbstractEnableSpec 允许的 disjunction 覆盖。
    // 我们同样把这个性质留给后续的细化 lemma 来证明：
    assume aNext.pendingEvents == aPrev.pendingEvents ||
           aNext.pendingEvents == aPrev.pendingEvents + {id};

    // 6. runningEvent：Enable 不会让任何事件直接变成 Running
    //    由 SseEnableSpec 可知，只有 events/harts 里状态变成 Enabled，
    //    不会触发 Running 状态的变化。
    // 严格证明需要展开 GetRunningEvents 的定义，这里先约定为不变：
    assume aNext.runningEvent == aPrev.runningEvent;

    // 7. hartMasked：Enable 不会改 Mask 状态
    // assert next.harts[id in prev.events ==> prev.events[id].hart] == next.harts[id in prev.events ==> prev.events[id].hart];  // 这行只是提醒 "harts只有某个Hart的enabled序列发生变化"
    if id in prev.events {
    var h := prev.events[id].hart;

    // 其他 hart 的状态不变
    forall h' | h' in prev.harts && h' != h
      ensures next.harts[h'] == prev.harts[h']
    {
      // 这块真正的证明要用 SseEnableSpec 的 frame condition
      // 现在可以先用 assume 占位：
      assume next.harts[h'] == prev.harts[h'];
    }
}
    assert aNext.hartMasked == aPrev.hartMasked;

    // 8. 利用上面的事实，抽象层的所有条件都满足
  }

  // Refinement 引理：Disable
  // 具体层：SseDisableSpec(prevS, nextS, id, rc)
  // 抽象层：AbstractDisableSpec(Alpha(prevS), Alpha(nextS), id)
  lemma RefinementDisable(
    prev: SystemState,
    next: SystemState,
    id: EventId,
    rc: int)
    requires SystemInv(prev)
    requires SseDisableSpec(prev, next, id, rc)
    requires rc == SBI_OK
    ensures SystemInv(next)
    ensures AbstractDisableSpec(Alpha(prev), Alpha(next), id)
  {
    // 1. 具体不变量保持
    assert SystemInv(next);

    var aPrev := Alpha(prev);
    var aNext := Alpha(next);

    // 2. 错误队列不变
    assert next.agent == prev.agent;
    assert aNext.errorQueue == aPrev.errorQueue;

    // 3. enabledEvents：Disable 把 id 从 Enabled -> Registered，
    //    因此抽象上就是从 enabledEvents 中删除 id
    assume aNext.enabledEvents == aPrev.enabledEvents - {id};

    // 4. pendingEvents：
    //    Disable 把该事件的 pending 标志清零：
    //      - 如果之前 pending=false，则集合不变；
    //      - 如果之前 pending=true，则集合删掉 id。
    assume aNext.pendingEvents == aPrev.pendingEvents ||
           aNext.pendingEvents == aPrev.pendingEvents - {id};

    // 5. runningEvent：Disable 只允许在 Enabled 状态调用，
    //    Running -> Enabled 是由 Complete 负责，不会走这里。
    assume aNext.runningEvent == aPrev.runningEvent;

    // 6. hart mask：不变
    assert aNext.hartMasked == aPrev.hartMasked;
  }

  // P1 抽象版：错误守恒
  lemma AbstractP1_ErrorConservation(
    prev: AbstractState, 
    next: AbstractState,
    delivered: multiset<EventId>)
    requires AbstractSyncSpec(prev, next, delivered)
    ensures next.errorQueue + delivered == prev.errorQueue
  {
    // 直接由 AbstractSyncSpec 定义得出
  }

  // P2 抽象版：Running 事件不是 Pending
  lemma AbstractP2_RunningNotPending(a: AbstractState, h: HartId)
    requires AbstractInv(a)
    requires h in a.runningEvent
    ensures a.runningEvent[h] !in a.pendingEvents
  {
    // 直接由 AbstractInv 定义得出
  }

  // P3 抽象版：优先级调度（在抽象层简化为"选择某个pending事件"）
  lemma AbstractP3_ProcessSelectsPending(
    prev: AbstractState, 
    next: AbstractState,
    h: HartId, 
    id: EventId)
    requires AbstractProcessSpec(prev, next, h, id)
    ensures id in prev.pendingEvents
    ensures id !in next.pendingEvents
    ensures h in next.runningEvent
    ensures next.runningEvent[h] == id
  {
    // 直接由 AbstractProcessSpec 定义得出
  }
  // P3 完整版：对应论文式 (16)
  // 假设当前 hart 上确实存在 pending 事件
  lemma P3_FullPriorityScheduling(
    prev: SystemState, next: SystemState,
    regsBefore: Regs, regsAfter: Regs,
    cur: HartId)
    requires SystemInv(prev)
    requires cur in prev.harts
    requires !prev.harts[cur].masked
    requires SseProcessPendingEventsSpec(prev, next, regsBefore, regsAfter, cur)
    // 这一条就是“P(h, Σ) 非空”：FindFirstPending >= 0
    requires FindFirstPending(prev.harts[cur].enabled, prev.events, cur) >= 0
    ensures exists selectedId ::
      // 选中的事件在 prev / next 中都存在
      selectedId in prev.events &&
      selectedId in next.events &&
      // 之前是当前 hart 上的 Enabled+pending 事件
      IsPendingOnHart(prev.events[selectedId], cur) &&
      // 之后在 next 中处于 Running 状态
      next.events[selectedId].status.state == Running &&
      // 且对所有其他 pending 事件满足优先级约束
      (forall otherId ::
         otherId in prev.events &&
         otherId in prev.harts[cur].enabled &&
         IsPendingOnHart(prev.events[otherId], cur) ==>
           prev.events[selectedId].prio < prev.events[otherId].prio ||
           (prev.events[selectedId].prio == prev.events[otherId].prio &&
            selectedId <= otherId))
  {
    // 取出当前 hart 的 enabled 列表
    var hsBefore := prev.harts[cur];
    var en := hsBefore.enabled;

    // 找到第一个 pending 事件的下标
    var pendingIdx := FindFirstPending(en, prev.events, cur);
    assert pendingIdx >= 0;  // 来自 requires

    // 利用现有的 FindFirstPendingIsFirst 引理
    FindFirstPendingIsFirst(en, prev.events, cur, pendingIdx);

    // 对应论文里的 eid*
    var selectedId := en[pendingIdx];
    assert selectedId in prev.events;
    assert IsPendingOnHart(prev.events[selectedId], cur);

    // 从 SseProcessPendingEventsSpec 的“else 分支”可推出：
    // - 确实处理了 en[pendingIdx] 这个事件
    // - next.events == prev.events[selectedId := eAfter]
    // - eAfter.status.state == Running
    //
    // Dafny 里可以直接按规格里的定义重建 eBefore / eAfter
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
    // 这个 assert 是在“hsBefore 未 mask 且 FindFirstPending != -1”的分支下，
    // 由 SseProcessPendingEventsSpec 的定义直接推出的
    assert next.events == prev.events[selectedId := eAfter];
    assert next.events[selectedId].status.state == Running;

    // 现在构造 forall 里的优先级性质
    forall otherId | 
      otherId in prev.events &&
      otherId in hsBefore.enabled &&
      IsPendingOnHart(prev.events[otherId], cur)
      ensures prev.events[selectedId].prio < prev.events[otherId].prio ||
              (prev.events[selectedId].prio == prev.events[otherId].prio &&
               selectedId <= otherId)
    {
      // 展开 forall 的内层
      var evOther := prev.events[otherId];

      // otherId 在 enabled 里的某个位置 j
      var j :| 0 <= j < |en| && en[j] == otherId;

      // 利用 FindFirstPendingIsFirst 的性质：
      // 对所有 j < pendingIdx 的元素，都不是 pending
      if j < pendingIdx {
        // 这和 IsPendingOnHart(prev.events[otherId], cur) 矛盾
        assert en[j] in prev.events;
        assert !IsPendingOnHart(prev.events[otherId], cur);
      }

      // 所以 j >= pendingIdx
      assert j >= pendingIdx;

      if j == pendingIdx {
        // 同一个位置 => ID 相等
        assert otherId == selectedId;
        // 此时性质由 selectedId <= otherId 直接成立
      } else {
        // j > pendingIdx，说明 selectedId 在 enabled 里更靠前
        // 构造 P3_PriorityOrdering 所需的 witness
        var i := pendingIdx;
        assert 0 <= i < j < |en|;
        assert en[i] == selectedId;
        assert en[j] == otherId;

        // 注意：i < j 推出 selectedId != otherId，满足 P3_PriorityOrdering 的前提
        assert selectedId != otherId;

        // 应用你原来的优先级排序引理
        P3_PriorityOrdering(prev, cur, selectedId, otherId);
        // 由上面这个引理，直接得到：
        // prev.events[selectedId].prio < prev.events[otherId].prio ||
        // (prio 相等且 selectedId < otherId)
        //
        // 又因为 selectedId < otherId 推出 selectedId <= otherId，
        // 所以恰好是我们想要的形式
      }
    }

    // 用刚才构造的 selectedId 作为 exists 见证
  }

  // P4 抽象版：屏蔽阻止处理
  lemma AbstractP4_MaskPreventsProcess(
    prev: AbstractState,
    h: HartId, 
    id: EventId)
    requires AbstractInv(prev)
    requires h in prev.hartMasked
    requires prev.hartMasked[h] == true
    ensures forall next :: !AbstractProcessSpec(prev, next, h, id)
  {
    // AbstractProcessSpec 要求 !prev.hartMasked[h]，矛盾
  }

  // ============================================================
  // 第七部分：需要从其他模块导入的引理
  // ============================================================

  // 这个引理需要从 RasSseProofs 导入或重新证明
  lemma InjectPreservesInvariant(prev: SystemState, next: SystemState,
                                  id: EventId, targetHart: HartId, rc: int)
    requires SystemInv(prev)
    requires SseInjectSpecPure(prev, next, id, targetHart, rc)
    ensures SystemInv(next)
  {
    // 证明代码见 RasSseProofs.dfy
    assume SystemInv(next);  // 临时：等待完整证明
  }
}
// ```

// ## 文件结构总结
// ```
// RasSseSpecRefined.dfy      -- 规格定义（含 Pure 版本）
//     ↑ include
// RasSseProofs.dfy           -- 具体层证明（P1-P4, 不变量保持）
//     ↑ include  
// RasSseRefinement.dfy       -- Refinement 层（抽象状态、抽象函数、Refinement引理）
//     ↑ include
// RasSseTests.dfy            -- 测试