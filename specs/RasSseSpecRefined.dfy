// ============================================================
// RasSseSpecRefined.dfy - RAS/SSE 形式化规格与证明
// ============================================================

module RasSseSpecRefined {

  // ============================================================
  // 第一部分：基本类型与常量
  // ============================================================

  type EventId = nat
  type HartId  = nat

  const MAX_EVENT_ID: nat := 1024
  const MAX_PEND_VECS: nat := 16
  const MAX_HARTS: nat := 64

  // SBI 返回码
  const SBI_OK: int               := 0
  const SBI_SUCCESS: int          := 0
  const SBI_ERR_FAILED: int       := -1
  const SBI_EFAIL: int            := -1
  const SBI_EINVAL: int           := -2
  const SBI_EINVALID_STATE: int   := -3
  const SBI_ENOTSUPP: int         := -4
  const SBI_EALREADY_STARTED: int := -5
  const SBI_EALREADY_STOPPED: int := -6

  // SSE 事件类型位
  const SBI_SSE_EVENT_GLOBAL_BIT: nat := 32768  // 1 << 15

  // 标准 SSE 事件 ID
  const SBI_SSE_EVENT_LOCAL_HIGH_PRIO_RAS: EventId := 0x0000
  const SBI_SSE_EVENT_GLOBAL_HIGH_PRIO_RAS: EventId := 0x8000

  // ============================================================
  // 第二部分：谓词与辅助函数
  // ============================================================

  predicate ValidEventId(e: EventId)
  {
    e < MAX_EVENT_ID
  }

  predicate ValidHartId(h: HartId)
  {
    h < MAX_HARTS
  }

  // 位操作抽象
  function IsGlobalEventFn(e: EventId): bool
  {
    ValidEventId(e) && (e / SBI_SSE_EVENT_GLOBAL_BIT) % 2 == 1
  }

  predicate IsGlobalEvent(e: EventId)
  {
    IsGlobalEventFn(e)
  }

  predicate IsHighPrioRasEvent(e: EventId)
  {
    e == SBI_SSE_EVENT_LOCAL_HIGH_PRIO_RAS ||
    e == SBI_SSE_EVENT_GLOBAL_HIGH_PRIO_RAS
  }

  // ============================================================
  // 第三部分：数据结构定义
  // ============================================================

  // 寄存器状态
  datatype Regs = Regs(
    mepc: nat,
    mstatus: nat,
    sepc: nat,
    hstatus: nat,
    a6: nat,
    a7: nat
  )

  predicate RegsInv(r: Regs)
  {
    true  // 可扩展添加约束
  }

  // SSE 事件状态机
  datatype SseState = Unused | Registered | Enabled | Running

  datatype SseStatus = SseStatus(
    state: SseState,
    pending: bool,
    injectable: bool
  )

  datatype SseEvent = SseEvent(
    id: EventId,
    status: SseStatus,
    prio: nat,
    hart: HartId,
    entryPc: nat,
    entryArg: nat,
    oneshot: bool,
    interruptedSepc: nat,
    interruptedFlags: nat,
    interruptedA6: nat,
    interruptedA7: nat
  )

  // 事件不变量
  predicate SseEventInv(e: SseEvent)
  {
    ValidEventId(e.id) &&
    (e.status.state == Running ==> !e.status.pending)
  }

  // Hart 状态
  datatype HartState = HartState(
    hart: HartId,
    masked: bool,
    enabled: seq<EventId>
  )

  // Hart 状态不变量
  predicate HartStateInv(hs: HartState, events: map<EventId, SseEvent>)
  {
    ValidHartId(hs.hart) &&
    // enabled 中每个 id 都必须存在且是 Enabled/Running 状态
    (forall i :: 0 <= i < |hs.enabled| ==>
      hs.enabled[i] in events &&
      SseEventInv(events[hs.enabled[i]]) &&
      events[hs.enabled[i]].status.state in {Enabled, Running}) &&
    // 按 (prio, id) 非降序排列
    (forall i, j :: 0 <= i < j < |hs.enabled| ==>
      hs.enabled[i] in events &&
      hs.enabled[j] in events &&
      (events[hs.enabled[i]].prio < events[hs.enabled[j]].prio ||
       (events[hs.enabled[i]].prio == events[hs.enabled[j]].prio && 
        hs.enabled[i] < hs.enabled[j])))
  }

  // RAS Agent 状态
  datatype RasAgent = RasAgent(
    registered: bool,
    probed: bool,
    regWidth: nat,
    hartErrs: seq<EventId>,
    devErrs: seq<EventId>
  )

  predicate RasAgentInv(a: RasAgent)
  {
    (!a.registered ==> !a.probed) &&
    (a.regWidth == 0 || a.regWidth == 32 || a.regWidth == 64) &&
    (forall e :: e in a.hartErrs ==> ValidEventId(e)) &&
    (forall e :: e in a.devErrs ==> ValidEventId(e))
  }

  // ============================================================
  // 第四部分：系统状态（使用 datatype 避免 class 的复杂性）
  // ============================================================

  datatype SystemState = SystemState(
    agent: RasAgent,
    events: map<EventId, SseEvent>,
    harts: map<HartId, HartState>
  )

  predicate SystemInv(s: SystemState)
  {
    RasAgentInv(s.agent) &&
    (forall id :: id in s.events ==> SseEventInv(s.events[id])) &&
    (forall h :: h in s.harts ==> HartStateInv(s.harts[h], s.events)) &&
    (forall e1, e2 ::
      e1 in s.events && e2 in s.events &&
      s.events[e1].status.state == Running &&
      s.events[e2].status.state == Running &&
      s.events[e1].hart == s.events[e2].hart ==> e1 == e2)
  }

  // 初始状态
  function InitialState(): SystemState
  {
    SystemState(
      RasAgent(false, false, 0, [], []),
      map[],
      map[]
    )
  }

  lemma InitialStateInv()
    ensures SystemInv(InitialState())
  {
    // 空映射平凡满足所有量化条件
  }

  // ============================================================
  // 第五部分：辅助函数
  // ============================================================

  // 序列成员关系
//     predicate InSeq<T(==)>(e: T, s: seq<T>)
//   {
//     exists i :: 0 <= i < |s| && s[i] == e
//   }
//   // 查找索引
//  function FindIndex<T(==)>(s: seq<T>, e: T): int
//     ensures FindIndex(s, e) >= -1
//     ensures FindIndex(s, e) < |s|
//     ensures FindIndex(s, e) >= 0 ==> s[FindIndex(s, e)] == e
//     //ensures FindIndex(s, e) == -1 ==> !InSeq(e, s)
// {
//      FindIndexHelper(s, e, 0)
// }
//   function FindIndexHelper<T(==)>(s: seq<T>, e: T, start: int): int
//     requires start >= 0
//     ensures FindIndexHelper(s, e, start) >= -1
//     ensures FindIndexHelper(s, e, start) < |s|
//     ensures FindIndexHelper(s, e, start) >= 0 ==> s[FindIndexHelper(s, e, start)] == e
//     decreases |s| - start
//   {
//     if start >= |s| then -1
//     else if s[start] == e then start
//     else FindIndexHelper(s, e, start + 1)
//   }
// 序列成员关系
predicate InSeq<T(==)>(e: T, s: seq<T>)
{
  exists i :: 0 <= i < |s| && s[i] == e
}

// 从 0 开始查找 e 的下标，如果不存在，就返回 -1
function FindIndex<T(==)>(s: seq<T>, e: T): int
  ensures -1 <= FindIndex(s, e) < |s|
  ensures FindIndex(s, e) >= 0 ==> s[FindIndex(s, e)] == e
{
  FindIndexHelper(s, e, 0)
}

function FindIndexHelper<T(==)>(s: seq<T>, e: T, start: int): int
  requires 0 <= start <= |s|
  ensures -1 <= FindIndexHelper(s, e, start) < |s|
  ensures FindIndexHelper(s, e, start) >= 0 ==>
            s[FindIndexHelper(s, e, start)] == e
  decreases |s| - start
{
  if start >= |s| then
    -1
  else if s[start] == e then
    start
  else
    FindIndexHelper(s, e, start + 1)
}
  // 多重集转换
  function ToMultiset(s: seq<EventId>): multiset<EventId>
  {
    if s == [] then multiset{} 
    else multiset{s[0]} + ToMultiset(s[1..])
  }

  // 按优先级插入（保持排序）
  function InsertSorted(en: seq<EventId>, id: EventId, evs: map<EventId, SseEvent>): seq<EventId>
  {
    if en == [] then
      [id]
    else if id in evs && en[0] in evs then
      var h := en[0];
      if evs[id].prio < evs[h].prio ||
         (evs[id].prio == evs[h].prio && id < h)
      then
        [id] + en
      else
        [h] + InsertSorted(en[1..], id, evs)
    else
      [id] + en  // fallback
  }

  // 移除元素
  function RemoveId(en: seq<EventId>, id: EventId): seq<EventId>
  {
    if en == [] then []
    else if en[0] == id then en[1..]
    else [en[0]] + RemoveId(en[1..], id)
  }

  // ============================================================
  // 第六部分：RAS Agent 规格
  // ============================================================

  predicate SbiRasGetAgentSpec(state: SystemState, result: RasAgent)
  {
    SystemInv(state) &&
    result == state.agent
  }

  predicate SbiRasSetAgentSpec(prev: SystemState, next: SystemState, 
                                newAgent: RasAgent, rc: int)
  {
    SystemInv(prev) && SystemInv(next) &&
    next.events == prev.events &&
    next.harts == prev.harts &&

    if prev.agent.registered then
      rc == SBI_EFAIL && next.agent == prev.agent
    else if !RasAgentInv(newAgent) then
      rc == SBI_EINVAL && next.agent == prev.agent
    else
      rc == SBI_OK &&
      next.agent == newAgent
  }

  predicate SbiRasProbeSpec(prev: SystemState, next: SystemState, rc: int)
  {
    SystemInv(prev) && SystemInv(next) &&
    next.events == prev.events &&
    next.harts == prev.harts &&

    if !prev.agent.registered then
      rc == SBI_EFAIL && next.agent == prev.agent
    else
      RasAgentInv(next.agent) &&
      next.agent.registered &&
      next.agent.probed &&
      (next.agent.regWidth == 32 || next.agent.regWidth == 64) &&
      rc == next.agent.regWidth &&
      next.agent.hartErrs == prev.agent.hartErrs &&
      next.agent.devErrs == prev.agent.devErrs
  }

  // 核心规格：Hart 错误同步
  predicate SbiRasSyncHartErrsSpec(
    prev: SystemState,
    next: SystemState,
    pending_vectors: seq<EventId>,
    nr_pending: nat,
    nr_remaining: nat,
    rc: int)
  {
    SystemInv(prev) && SystemInv(next) &&
    next.events == prev.events &&
    next.harts == prev.harts &&

    if !prev.agent.registered then
      rc == SBI_EFAIL &&
      next.agent == prev.agent &&
      nr_pending == 0 &&
      nr_remaining == 0 &&
      |pending_vectors| == 0
    else
      rc == SBI_OK &&
      nr_pending <= MAX_PEND_VECS &&
      nr_pending <= |prev.agent.hartErrs| &&
      |pending_vectors| == nr_pending &&
      pending_vectors == prev.agent.hartErrs[..nr_pending] &&
      nr_remaining == |prev.agent.hartErrs| - nr_pending &&
      next.agent.hartErrs == prev.agent.hartErrs[nr_pending..] &&
      next.agent.devErrs == prev.agent.devErrs &&
      next.agent.regWidth == prev.agent.regWidth &&
      next.agent.registered == prev.agent.registered &&
      next.agent.probed == prev.agent.probed
  }

  // 设备错误同步
  predicate SbiRasSyncDevErrsSpec(
    prev: SystemState,
    next: SystemState,
    pending_vectors: seq<EventId>,
    nr_pending: nat,
    nr_remaining: nat,
    rc: int)
  {
    SystemInv(prev) && SystemInv(next) &&
    next.events == prev.events &&
    next.harts == prev.harts &&

    if !prev.agent.registered then
      rc == SBI_EFAIL &&
      next.agent == prev.agent &&
      nr_pending == 0 &&
      nr_remaining == 0 &&
      |pending_vectors| == 0
    else
      rc == SBI_OK &&
      nr_pending <= MAX_PEND_VECS &&
      nr_pending <= |prev.agent.devErrs| &&
      |pending_vectors| == nr_pending &&
      pending_vectors == prev.agent.devErrs[..nr_pending] &&
      nr_remaining == |prev.agent.devErrs| - nr_pending &&
      next.agent.devErrs == prev.agent.devErrs[nr_pending..] &&
      next.agent.hartErrs == prev.agent.hartErrs &&
      next.agent.regWidth == prev.agent.regWidth &&
      next.agent.registered == prev.agent.registered &&
      next.agent.probed == prev.agent.probed
  }

  // ============================================================
  // 第七部分：SSE 事件管理规格
  // ============================================================

  // 添加事件
  predicate SseAddEventSpec(prev: SystemState, next: SystemState,
                            id: EventId, hart: HartId, prio: nat, rc: int)
  {
    SystemInv(prev) &&

    if !ValidEventId(id) || !ValidHartId(hart) then
      rc == SBI_EINVAL && next == prev
    else if id in prev.events then
      rc == SBI_EINVAL && next == prev
    else
      rc == SBI_OK &&
      var newEv := SseEvent(
        id,
        SseStatus(Unused, false, false),
        prio,
        hart,
        0, 0,  // entryPc, entryArg
        false, // oneshot
        0, 0, 0, 0  // interrupted context
      );
      next.events == prev.events[id := newEv] &&
      next.agent == prev.agent &&
      next.harts == prev.harts &&
      SystemInv(next)
  }

  // 注册事件
  predicate SseRegisterSpec(prev: SystemState, next: SystemState,
                            id: EventId, pc: nat, arg: nat, rc: int)
  {
    SystemInv(prev) &&
    next.agent == prev.agent &&
    next.harts == prev.harts &&

    if id !in prev.events then
      rc == SBI_EINVAL && next.events == prev.events
    else if prev.events[id].status.state != Unused then
      rc == SBI_EINVALID_STATE && next.events == prev.events
    else
      rc == SBI_OK &&
      var eBefore := prev.events[id];
      var eAfter := SseEvent(
        eBefore.id,
        SseStatus(Registered, false, true),
        eBefore.prio,
        eBefore.hart,
        pc, arg,
        eBefore.oneshot,
        0, 0, 0, 0
      );
      next.events == prev.events[id := eAfter] &&
      SystemInv(next)
  }

  // 启用事件
  predicate SseEnableSpec(prev: SystemState, next: SystemState, 
                          id: EventId, rc: int)
  {
    SystemInv(prev) &&
    next.agent == prev.agent &&

    if id !in prev.events then
      rc == SBI_EINVAL &&
      next.events == prev.events &&
      next.harts == prev.harts
    else if prev.events[id].status.state != Registered then
      rc == SBI_EINVALID_STATE &&
      next.events == prev.events &&
      next.harts == prev.harts
    else
      var eBefore := prev.events[id];
      var h := eBefore.hart;
      
      if h !in prev.harts then
        rc == SBI_EINVAL &&
        next.events == prev.events &&
        next.harts == prev.harts
      else
        rc == SBI_OK &&
        var eAfter := SseEvent(
          eBefore.id,
          SseStatus(Enabled, eBefore.status.pending, eBefore.status.injectable),
          eBefore.prio,
          eBefore.hart,
          eBefore.entryPc, eBefore.entryArg,
          eBefore.oneshot,
          eBefore.interruptedSepc, eBefore.interruptedFlags,
          eBefore.interruptedA6, eBefore.interruptedA7
        );
        next.events == prev.events[id := eAfter] &&
        
        var hsBefore := prev.harts[h];
        var hsAfter := HartState(
          hsBefore.hart,
          hsBefore.masked,
          InsertSorted(hsBefore.enabled, id, next.events)
        );
        next.harts == prev.harts[h := hsAfter] &&
        SystemInv(next)
  }

  // 禁用事件
  predicate SseDisableSpec(prev: SystemState, next: SystemState,
                           id: EventId, rc: int)
  {
    SystemInv(prev) &&
    next.agent == prev.agent &&

    if id !in prev.events then
      rc == SBI_EINVAL &&
      next.events == prev.events &&
      next.harts == prev.harts
    else
      var eBefore := prev.events[id];
      if eBefore.status.state != Enabled then
        rc == SBI_EINVALID_STATE &&
        next.events == prev.events &&
        next.harts == prev.harts
      else
        var h := eBefore.hart;
        if h !in prev.harts then
          rc == SBI_EINVAL &&
          next.events == prev.events &&
          next.harts == prev.harts
        else
          rc == SBI_OK &&
          var eAfter := SseEvent(
            eBefore.id,
            SseStatus(Registered, false, eBefore.status.injectable),
            eBefore.prio,
            eBefore.hart,
            eBefore.entryPc, eBefore.entryArg,
            eBefore.oneshot,
            eBefore.interruptedSepc, eBefore.interruptedFlags,
            eBefore.interruptedA6, eBefore.interruptedA7
          );
          next.events == prev.events[id := eAfter] &&
          
          var hsBefore := prev.harts[h];
          var hsAfter := HartState(
            hsBefore.hart,
            hsBefore.masked,
            RemoveId(hsBefore.enabled, id)
          );
          next.harts == prev.harts[h := hsAfter] &&
          SystemInv(next)
  }

  // 注入事件（修正版：只允许 Enabled 状态）
  predicate SseInjectSpec(prev: SystemState, next: SystemState,
                          id: EventId, targetHart: HartId, rc: int)
  {
    SystemInv(prev) &&
    next.agent == prev.agent &&
    next.harts == prev.harts &&

    if id !in prev.events then
      rc == SBI_EINVAL &&
      next.events == prev.events
    else
      var eBefore := prev.events[id];
      // 修正：只允许 Enabled 状态，不允许 Running
      if eBefore.status.state != Enabled then
        rc == SBI_EINVALID_STATE &&
        next.events == prev.events
      else
        rc == SBI_OK &&
        var newHart := if IsGlobalEvent(id) then targetHart else eBefore.hart;
        var eAfter := SseEvent(
          eBefore.id,
          SseStatus(Enabled, true, eBefore.status.injectable),  // pending = true
          eBefore.prio,
          newHart,
          eBefore.entryPc, eBefore.entryArg,
          eBefore.oneshot,
          eBefore.interruptedSepc, eBefore.interruptedFlags,
          eBefore.interruptedA6, eBefore.interruptedA7
        );
        next.events == prev.events[id := eAfter] &&
        SystemInv(next)
  }

  // 处理 pending 事件
  predicate SseProcessPendingEventsSpec(
    prev: SystemState, 
    next: SystemState,
    regsBefore: Regs, 
    regsAfter: Regs,
    cur: HartId)
  {
    SystemInv(prev) &&
    RegsInv(regsBefore) &&
    cur in prev.harts &&

    var hsBefore := prev.harts[cur];

    // 如果 hart 被屏蔽，不处理
    if hsBefore.masked then
      next == prev && regsAfter == regsBefore
    else
      var en := hsBefore.enabled;
      
      // 查找第一个 pending 的 Enabled 事件
      var pendingIdx := FindFirstPending(en, prev.events, cur);
      
      if pendingIdx == -1 then
        // 没有 pending 事件
        next == prev && regsAfter == regsBefore
      else
        // 处理找到的事件
        var id := en[pendingIdx];
        id in prev.events &&
        var eBefore := prev.events[id];
        
        // 转换到 Running 状态
        var eAfter := SseEvent(
          eBefore.id,
          SseStatus(Running, false, eBefore.status.injectable),  // pending = false
          eBefore.prio,
          eBefore.hart,
          eBefore.entryPc, eBefore.entryArg,
          eBefore.oneshot,
          regsBefore.sepc,    // 保存中断上下文
          0,
          regsBefore.a6,
          regsBefore.a7
        );
        
        next.events == prev.events[id := eAfter] &&
        next.agent == prev.agent &&
        next.harts == prev.harts &&
        
        // 寄存器切换到处理程序
        regsAfter.mepc == eBefore.entryPc &&
        regsAfter.a7 == eBefore.entryArg &&
        RegsInv(regsAfter) &&
        SystemInv(next)
  }

  // 查找第一个 pending 事件
  function FindFirstPending(en: seq<EventId>, evs: map<EventId, SseEvent>, cur: HartId): int
    ensures FindFirstPending(en, evs, cur) >= -1
    ensures FindFirstPending(en, evs, cur) < |en|
  {
    FindFirstPendingHelper(en, evs, cur, 0)
  }

  function FindFirstPendingHelper(en: seq<EventId>, evs: map<EventId, SseEvent>, 
                                   cur: HartId, start: int): int
    requires start >= 0
    ensures FindFirstPendingHelper(en, evs, cur, start) >= -1
    ensures FindFirstPendingHelper(en, evs, cur, start) < |en|
    decreases |en| - start
  {
    if start >= |en| then -1
    else if en[start] in evs then
      var ev := evs[en[start]];
      if ev.status.state == Enabled && ev.status.pending && ev.hart == cur
      then start
      else FindFirstPendingHelper(en, evs, cur, start + 1)
    else FindFirstPendingHelper(en, evs, cur, start + 1)
  }

  // 完成事件处理
  predicate SseCompleteSpec(
    prev: SystemState, 
    next: SystemState,
    regsBefore: Regs, 
    regsAfter: Regs,
    cur: HartId, 
    rc: int)
  {
    SystemInv(prev) &&
    RegsInv(regsBefore) &&
    cur in prev.harts &&

    var hsBefore := prev.harts[cur];
    
    // 查找 Running 状态的事件
    var runningIdx := FindFirstRunning(hsBefore.enabled, prev.events, cur);
    
    if runningIdx == -1 then
      // 没有 Running 事件
      rc == SBI_EINVALID_STATE &&
      next == prev &&
      regsAfter == regsBefore
    else
      var id := hsBefore.enabled[runningIdx];
      id in prev.events &&
      var eBefore := prev.events[id];
      
      rc == SBI_OK &&
      
      // 根据 oneshot 决定下一个状态
      var nextState := if eBefore.oneshot then Registered else Enabled;
      var eAfter := SseEvent(
        eBefore.id,
        SseStatus(nextState, false, eBefore.status.injectable),
        eBefore.prio,
        eBefore.hart,
        eBefore.entryPc, eBefore.entryArg,
        eBefore.oneshot,
        0, 0, 0, 0  // 清除中断上下文
      );
      
      next.events == prev.events[id := eAfter] &&
      next.agent == prev.agent &&
      
      // 如果是 oneshot，从 enabled 列表移除
      var hsAfter := HartState(
        hsBefore.hart,
        hsBefore.masked,
        if eBefore.oneshot then RemoveId(hsBefore.enabled, id) else hsBefore.enabled
      );
      next.harts == prev.harts[cur := hsAfter] &&
      
      // 恢复寄存器
      regsAfter.sepc == eBefore.interruptedSepc &&
      regsAfter.a6 == eBefore.interruptedA6 &&
      regsAfter.a7 == eBefore.interruptedA7 &&
      RegsInv(regsAfter) &&
      SystemInv(next)
  }

  // 查找第一个 Running 事件
  function FindFirstRunning(en: seq<EventId>, evs: map<EventId, SseEvent>, cur: HartId): int
    ensures FindFirstRunning(en, evs, cur) >= -1
    ensures FindFirstRunning(en, evs, cur) < |en|
  {
    FindFirstRunningHelper(en, evs, cur, 0)
  }

  function FindFirstRunningHelper(en: seq<EventId>, evs: map<EventId, SseEvent>,
                                   cur: HartId, start: int): int
    requires start >= 0
    ensures FindFirstRunningHelper(en, evs, cur, start) >= -1
    ensures FindFirstRunningHelper(en, evs, cur, start) < |en|
    decreases |en| - start
  {
    if start >= |en| then -1
    else if en[start] in evs then
      var ev := evs[en[start]];
      if ev.status.state == Running && ev.hart == cur
      then start
      else FindFirstRunningHelper(en, evs, cur, start + 1)
    else FindFirstRunningHelper(en, evs, cur, start + 1)
  }

  // ============================================================
  // 第八部分：Hart 屏蔽规格
  // ============================================================

  predicate SseHartMaskSpec(prev: SystemState, next: SystemState, 
                            cur: HartId, rc: int)
  {
    SystemInv(prev) &&
    next.agent == prev.agent &&
    next.events == prev.events &&

    if cur !in prev.harts then
      rc == SBI_EINVAL && next.harts == prev.harts
    else if prev.harts[cur].masked then
      rc == SBI_EALREADY_STOPPED && next.harts == prev.harts
    else
      rc == SBI_SUCCESS &&
      var hsBefore := prev.harts[cur];
      var hsAfter := HartState(hsBefore.hart, true, hsBefore.enabled);
      next.harts == prev.harts[cur := hsAfter] &&
      SystemInv(next)
  }

  predicate SseHartUnmaskSpec(prev: SystemState, next: SystemState,
                              cur: HartId, rc: int)
  {
    SystemInv(prev) &&
    next.agent == prev.agent &&
    next.events == prev.events &&

    if cur !in prev.harts then
      rc == SBI_EINVAL && next.harts == prev.harts
    else if !prev.harts[cur].masked then
      rc == SBI_EALREADY_STARTED && next.harts == prev.harts
    else
      rc == SBI_SUCCESS &&
      var hsBefore := prev.harts[cur];
      var hsAfter := HartState(hsBefore.hart, false, hsBefore.enabled);
      next.harts == prev.harts[cur := hsAfter] &&
      SystemInv(next)
  }

  // ============================================================
  // 第九部分：RAS 处理规格
  // ============================================================

  predicate RasProcessSpec(
    prev: SystemState, 
    next: SystemState,
    cur: HartId,
    pending_vectors: seq<EventId>,
    nr_pending: nat,
    nr_remaining: nat,
    rcSync: int,
    mid: SystemState)
  {
    SystemInv(prev) &&
    cur in prev.harts &&

    // 第一步：同步错误
    SbiRasSyncHartErrsSpec(prev, mid, pending_vectors, nr_pending, nr_remaining, rcSync) &&

    // 第二步：注入高优先级事件
    (rcSync != SBI_OK ==> next == mid) &&
    (rcSync == SBI_OK ==>
      next.agent == mid.agent &&
      next.harts == mid.harts &&
      SystemInv(next) &&
      // 所有高优先级 RAS 事件被标记为 pending
      (forall i :: 0 <= i < nr_pending ==>
        IsHighPrioRasEvent(pending_vectors[i]) ==>
          pending_vectors[i] in next.events &&
          next.events[pending_vectors[i]].status.pending))
  }
}
