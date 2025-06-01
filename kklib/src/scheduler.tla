------------------------------- MODULE scheduler -------------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT Ps, maxtasks, maxcounter, NULL



(*--algorithm scheduler
variables
    stopped = FALSE,
    counter = 1,
    gq = 1..counter,
    signaled = gq,
    lq_size = 4,
    lq = [plq \in Ps |-> {}],
    ret = [pret \in Ps |-> NULL],
    idle = {},
    idle_count = 0,
    spinning_count = 0,
    parking_slot = [pps \in Ps |-> 0],
    done = {},
    processes = [pss \in Ps |-> "running"],
    slock = 0;

procedure lock() begin
Lock:
    await slock = 0;
    slock := 1;
    return;
end procedure;

procedure unlock() begin
Unlock:
    slock := 0;
    return;
end procedure;

procedure prepare_park() begin
PreparePark:
    ret[self] := parking_slot[self];
    return;
end procedure;

procedure park_on(epoch) begin
ParkOn:
    assert epoch \in Nat;
    await epoch /= parking_slot[self] \/ stopped;
    return;
end procedure;

procedure wake_p(p) begin
WakeP:
    parking_slot[p] := parking_slot[self] + 1;
    return;
end procedure;

procedure lq_put(task) begin
LqPut:
assert task \in Nat;
if Cardinality(lq[self]) = lq_size then
lq[self] := lq[self] \union {task};
ret[self] := TRUE;
else
ret[self] := FALSE;
end if;
return;
end procedure;

procedure lq_put_bulk(tasks) begin
LqPutBulk:
assert \A lqtask \in tasks: lqtask \in Nat;
assert lq[self] = {};
lq[self] := lq[self] \union tasks;
return;
end procedure;

procedure lq_get() begin
LqGet:
if Cardinality(lq[self]) = 0 then
ret[self] := NULL;
else
with lqgtask = CHOOSE t \in lq[self]: TRUE do
assert lqgtask \in Nat;
lq[self] := lq[self] \ {lqgtask};
ret[self] := lqgtask;
end with;
end if;
return;
end procedure;

procedure lq_steal(victim) begin
LqSteal:
with num_to_grab = (Cardinality(lq[victim]) + 1) \div 2 do
with stolen_tasks = (CHOOSE t \in SUBSET lq[victim]: (Cardinality(t) = num_to_grab)) do
lq[victim] := lq[victim] \ stolen_tasks;
ret[self] := stolen_tasks;
end with; 
end with;
return;
end procedure;

procedure gq_put(tasks) begin
GqPut:
    assert \A gqtask \in tasks: gqtask \in Nat;
    gq := gq \union tasks;
    return;
end procedure;

procedure grab_from_gq()
variables num_to_grab_gq = lq_size;
begin
GrabFromGq:
    with ntg = (Cardinality(gq) + Cardinality(Ps) - 1) \div Cardinality(Ps) do
    if ntg < num_to_grab_gq then
    num_to_grab_gq := ntg;
    end if; 
    with grabbed_tasks = (CHOOSE t \in SUBSET gq: (Cardinality(t) = num_to_grab_gq)) do
    if grabbed_tasks = {} then
    ret[self] := NULL;
    else
    with single_task = CHOOSE t1 \in grabbed_tasks: TRUE do
    ret[self] := single_task;
    call lq_put_bulk(grabbed_tasks \ {single_task});
    end with;
    end if;
    end with;
    end with;
    gfgl0: return;
end procedure;
    
    

procedure try_from_gq()
begin
TryFromGq:
if gq = {} then
    ret[self] := NULL
else
    with tftask = CHOOSE t \in gq: TRUE do
    gq := gq \ {tftask};
    ret[self] := tftask;
    end with;
end if;
return;
end procedure;

procedure try_steal()
variable localp = NULL,
localtask = NULL;
begin
TrySteal:
with pts \in {ppts \in Ps: ppts /= self} do
localp := pts;
end with;
call lq_steal(localp);
tsl0: if ret[self] = {} then
ret[self] := NULL;
else
with tstask = CHOOSE t \in ret[self]: TRUE do
localtask := tstask;
end with;
ret[self] := ret[self] \ {localtask};
call lq_put_bulk(ret[self]);
tsl1: ret[self] := localtask;
end if;
tsl2: return;
end procedure;

procedure start_spinning()
begin
StartSpinning:
if spinning_count < (Cardinality(Ps) \div 2) then
IncSpin:
spinning_count := spinning_count + 1;
ret[self] := TRUE;
else
ret[self] := FALSE;
end if;
ssl1: return;
end procedure;

procedure stop_spinning()
begin
StopSpinning:
assert spinning_count > 0;
ret[self] := (spinning_count = 1);
spinning_count := spinning_count - 1;
return;
end procedure;

procedure anounce_park()
begin
AnouncePark:
call lock();
apl0: idle := idle \union {self};
apl1: idle_count := idle_count + 1;
call unlock();
return;
end procedure;

procedure anounce_unpark()
begin
AnounceUnpark:
call lock();
aul0:if self \in idle then
aul1: idle := idle \ {self};
aul2: idle_count := idle_count - 1;
end if;
aul3:
call unlock();
return;
end procedure;

procedure wake_worker()
variable localp = NULL;
begin
WakeWorker:
call lock();
wwl0: with wwp \in idle do
localp := wwp;
end with;
wwl1: idle := idle \ {localp};
wwl2: idle_count := idle_count - 1;
call wake_p(p);
wwl3: call unlock();
return;
end procedure;

procedure try_pick_task()
variables curtask = NULL;
begin
TryPickTask:
    either
    call try_from_gq();
    tptl0: if ret[self] /= NULL then return; end if;
    or
    skip;
    end either;
    tptl1: call lq_get();
    tptl2: if ret[self] /= NULL then return; end if;
    tptl3: call grab_from_gq();
    tptl4: if ret[self] /= NULL then return; end if;
    tptl5: call start_spinning();
    tptl6: if ret[self] then \* can start spinning
    call try_steal();
    tptl7: curtask := ret[self];
    call stop_spinning(); \* returns am i last_spinner
        tptl8: if curtask /= NULL /\ ret[self] then
            call wake_worker(); \* i was the last spinner, so i need to wake next worker
        end if;
    end if;
    tptl9: ret[self] := curtask;
    return;
end procedure;

procedure try_pick_task_before_park()
begin
TryPickTaskBeforePark:
call try_from_gq();
tptl0: if ret[self] /= NULL then return; end if;
tptl1: call try_steal();
return;
end procedure;

procedure signal_task()
begin
SignalTask:
if spinning_count = 0 /\ idle_count > 0 then
call wake_worker();
end if;
stl0: return;
end procedure;

procedure put_task(task) begin
ptl0:
assert task \in Nat;
either
call gq_put({task});
or
call lq_put(task);
ptl1: if ret[self] /= TRUE then
call lq_steal(self);
ptl2: ret[self] := ret[self] \union {task};
call gq_put(ret[self]);
end if; 
end either;
tpl3: return;
end procedure;

procedure push_task()
variables lcnt = 0;
begin
PushTask:
    if stopped \/ counter > maxcounter then return; end if;
    tpl4: counter := counter + 1;
    lcnt := counter;
    call put_task(lcnt);
Signal:
    call signal_task();
    tpl5: signaled := signaled \union {lcnt};
    return;
end procedure;

procedure run_task(task)
variables maxtasksl = 0;
begin
RunTask:
    done := done \union {task};
    with numtasks \in 0..maxtasks do
    maxtasksl := numtasks;
    end with;
pushtask:
    while maxtasksl > 0 do
        maxtasksl := maxtasksl - 1;
        call push_task();
    end while;
    return;
end procedure;

fair process ps \in Ps
variables
epoch = 0;
begin
RunLoop:
call try_pick_task();
rll0:
if ret[self] /= NULL then 
    call run_task(ret[self]);
    goto RunLoop;
else
    call prepare_park();
    rll1: epoch := ret[self];
    call anounce_park();
    rll2: call try_pick_task_before_park();
    rll3: if ret[self] /= NULL then
       call anounce_unpark();
       rll4: call run_task(ret[self]);
       rll5: goto RunLoop;
    else
       call park_on(epoch); 
    end if;
end if;
rll6: if stopped then goto Done; end if;
rll7: goto RunLoop;
end process;

fair+ process stopper = "stopper"
begin
Stopper:
await (\A prs \in Ps: pc[prs] = "ParkOn" /\ lq[prs] = {}) /\ gq = {};
stopped := TRUE;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "eed4be64" /\ chksum(tla) = "b7260afe")
\* Label tptl0 of procedure try_pick_task at line 235 col 12 changed to tptl0_
\* Label tptl1 of procedure try_pick_task at line 239 col 12 changed to tptl1_
\* Process variable epoch of process ps at line 322 col 1 changed to epoch_
\* Procedure variable localp of procedure try_steal at line 148 col 10 changed to localp_
\* Parameter task of procedure lq_put at line 57 col 18 changed to task_
\* Parameter tasks of procedure lq_put_bulk at line 69 col 23 changed to tasks_
\* Parameter task of procedure put_task at line 274 col 20 changed to task_p
CONSTANT defaultInitValue
VARIABLES stopped, counter, gq, signaled, lq_size, lq, ret, idle, idle_count, 
          spinning_count, parking_slot, done, processes, slock, pc, stack, 
          epoch, p, task_, tasks_, victim, tasks, num_to_grab_gq, localp_, 
          localtask, localp, curtask, task_p, lcnt, task, maxtasksl, epoch_

vars == << stopped, counter, gq, signaled, lq_size, lq, ret, idle, idle_count, 
           spinning_count, parking_slot, done, processes, slock, pc, stack, 
           epoch, p, task_, tasks_, victim, tasks, num_to_grab_gq, localp_, 
           localtask, localp, curtask, task_p, lcnt, task, maxtasksl, epoch_
        >>

ProcSet == (Ps) \cup {"stopper"}

Init == (* Global variables *)
        /\ stopped = FALSE
        /\ counter = 1
        /\ gq = 1..counter
        /\ signaled = gq
        /\ lq_size = 4
        /\ lq = [plq \in Ps |-> {}]
        /\ ret = [pret \in Ps |-> NULL]
        /\ idle = {}
        /\ idle_count = 0
        /\ spinning_count = 0
        /\ parking_slot = [pps \in Ps |-> 0]
        /\ done = {}
        /\ processes = [pss \in Ps |-> "running"]
        /\ slock = 0
        (* Procedure park_on *)
        /\ epoch = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure wake_p *)
        /\ p = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure lq_put *)
        /\ task_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure lq_put_bulk *)
        /\ tasks_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure lq_steal *)
        /\ victim = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure gq_put *)
        /\ tasks = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure grab_from_gq *)
        /\ num_to_grab_gq = [ self \in ProcSet |-> lq_size]
        (* Procedure try_steal *)
        /\ localp_ = [ self \in ProcSet |-> NULL]
        /\ localtask = [ self \in ProcSet |-> NULL]
        (* Procedure wake_worker *)
        /\ localp = [ self \in ProcSet |-> NULL]
        (* Procedure try_pick_task *)
        /\ curtask = [ self \in ProcSet |-> NULL]
        (* Procedure put_task *)
        /\ task_p = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure push_task *)
        /\ lcnt = [ self \in ProcSet |-> 0]
        (* Procedure run_task *)
        /\ task = [ self \in ProcSet |-> defaultInitValue]
        /\ maxtasksl = [ self \in ProcSet |-> 0]
        (* Process ps *)
        /\ epoch_ = [self \in Ps |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Ps -> "RunLoop"
                                        [] self = "stopper" -> "Stopper"]

Lock(self) == /\ pc[self] = "Lock"
              /\ slock = 0
              /\ slock' = 1
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, epoch, p, task_, tasks_, victim, 
                              tasks, num_to_grab_gq, localp_, localtask, 
                              localp, curtask, task_p, lcnt, task, maxtasksl, 
                              epoch_ >>

lock(self) == Lock(self)

Unlock(self) == /\ pc[self] = "Unlock"
                /\ slock' = 0
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                                ret, idle, idle_count, spinning_count, 
                                parking_slot, done, processes, epoch, p, task_, 
                                tasks_, victim, tasks, num_to_grab_gq, localp_, 
                                localtask, localp, curtask, task_p, lcnt, task, 
                                maxtasksl, epoch_ >>

unlock(self) == Unlock(self)

PreparePark(self) == /\ pc[self] = "PreparePark"
                     /\ ret' = [ret EXCEPT ![self] = parking_slot[self]]
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, 
                                     lq, idle, idle_count, spinning_count, 
                                     parking_slot, done, processes, slock, 
                                     epoch, p, task_, tasks_, victim, tasks, 
                                     num_to_grab_gq, localp_, localtask, 
                                     localp, curtask, task_p, lcnt, task, 
                                     maxtasksl, epoch_ >>

prepare_park(self) == PreparePark(self)

ParkOn(self) == /\ pc[self] = "ParkOn"
                /\ Assert(epoch[self] \in Nat, 
                          "Failure of assertion at line 46, column 5.")
                /\ epoch[self] /= parking_slot[self] \/ stopped
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ epoch' = [epoch EXCEPT ![self] = Head(stack[self]).epoch]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                                ret, idle, idle_count, spinning_count, 
                                parking_slot, done, processes, slock, p, task_, 
                                tasks_, victim, tasks, num_to_grab_gq, localp_, 
                                localtask, localp, curtask, task_p, lcnt, task, 
                                maxtasksl, epoch_ >>

park_on(self) == ParkOn(self)

WakeP(self) == /\ pc[self] = "WakeP"
               /\ parking_slot' = [parking_slot EXCEPT ![p[self]] = parking_slot[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                               ret, idle, idle_count, spinning_count, done, 
                               processes, slock, epoch, task_, tasks_, victim, 
                               tasks, num_to_grab_gq, localp_, localtask, 
                               localp, curtask, task_p, lcnt, task, maxtasksl, 
                               epoch_ >>

wake_p(self) == WakeP(self)

LqPut(self) == /\ pc[self] = "LqPut"
               /\ Assert(task_[self] \in Nat, 
                         "Failure of assertion at line 59, column 1.")
               /\ IF Cardinality(lq[self]) = lq_size
                     THEN /\ lq' = [lq EXCEPT ![self] = lq[self] \union {task_[self]}]
                          /\ ret' = [ret EXCEPT ![self] = TRUE]
                     ELSE /\ ret' = [ret EXCEPT ![self] = FALSE]
                          /\ lq' = lq
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ task_' = [task_ EXCEPT ![self] = Head(stack[self]).task_]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, idle, 
                               idle_count, spinning_count, parking_slot, done, 
                               processes, slock, epoch, p, tasks_, victim, 
                               tasks, num_to_grab_gq, localp_, localtask, 
                               localp, curtask, task_p, lcnt, task, maxtasksl, 
                               epoch_ >>

lq_put(self) == LqPut(self)

LqPutBulk(self) == /\ pc[self] = "LqPutBulk"
                   /\ Assert(\A lqtask \in tasks_[self]: lqtask \in Nat, 
                             "Failure of assertion at line 71, column 1.")
                   /\ Assert(lq[self] = {}, 
                             "Failure of assertion at line 72, column 1.")
                   /\ lq' = [lq EXCEPT ![self] = lq[self] \union tasks_[self]]
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ tasks_' = [tasks_ EXCEPT ![self] = Head(stack[self]).tasks_]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, 
                                   ret, idle, idle_count, spinning_count, 
                                   parking_slot, done, processes, slock, epoch, 
                                   p, task_, victim, tasks, num_to_grab_gq, 
                                   localp_, localtask, localp, curtask, task_p, 
                                   lcnt, task, maxtasksl, epoch_ >>

lq_put_bulk(self) == LqPutBulk(self)

LqGet(self) == /\ pc[self] = "LqGet"
               /\ IF Cardinality(lq[self]) = 0
                     THEN /\ ret' = [ret EXCEPT ![self] = NULL]
                          /\ lq' = lq
                     ELSE /\ LET lqgtask == CHOOSE t \in lq[self]: TRUE IN
                               /\ Assert(lqgtask \in Nat, 
                                         "Failure of assertion at line 83, column 1.")
                               /\ lq' = [lq EXCEPT ![self] = lq[self] \ {lqgtask}]
                               /\ ret' = [ret EXCEPT ![self] = lqgtask]
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, idle, 
                               idle_count, spinning_count, parking_slot, done, 
                               processes, slock, epoch, p, task_, tasks_, 
                               victim, tasks, num_to_grab_gq, localp_, 
                               localtask, localp, curtask, task_p, lcnt, task, 
                               maxtasksl, epoch_ >>

lq_get(self) == LqGet(self)

LqSteal(self) == /\ pc[self] = "LqSteal"
                 /\ LET num_to_grab == (Cardinality(lq[victim[self]]) + 1) \div 2 IN
                      LET stolen_tasks == (CHOOSE t \in SUBSET lq[victim[self]]: (Cardinality(t) = num_to_grab)) IN
                        /\ lq' = [lq EXCEPT ![victim[self]] = lq[victim[self]] \ stolen_tasks]
                        /\ ret' = [ret EXCEPT ![self] = stolen_tasks]
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ victim' = [victim EXCEPT ![self] = Head(stack[self]).victim]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, idle, 
                                 idle_count, spinning_count, parking_slot, 
                                 done, processes, slock, epoch, p, task_, 
                                 tasks_, tasks, num_to_grab_gq, localp_, 
                                 localtask, localp, curtask, task_p, lcnt, 
                                 task, maxtasksl, epoch_ >>

lq_steal(self) == LqSteal(self)

GqPut(self) == /\ pc[self] = "GqPut"
               /\ Assert(\A gqtask \in tasks[self]: gqtask \in Nat, 
                         "Failure of assertion at line 104, column 5.")
               /\ gq' = (gq \union tasks[self])
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ tasks' = [tasks EXCEPT ![self] = Head(stack[self]).tasks]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << stopped, counter, signaled, lq_size, lq, ret, 
                               idle, idle_count, spinning_count, parking_slot, 
                               done, processes, slock, epoch, p, task_, tasks_, 
                               victim, num_to_grab_gq, localp_, localtask, 
                               localp, curtask, task_p, lcnt, task, maxtasksl, 
                               epoch_ >>

gq_put(self) == GqPut(self)

GrabFromGq(self) == /\ pc[self] = "GrabFromGq"
                    /\ LET ntg == (Cardinality(gq) + Cardinality(Ps) - 1) \div Cardinality(Ps) IN
                         /\ IF ntg < num_to_grab_gq[self]
                               THEN /\ num_to_grab_gq' = [num_to_grab_gq EXCEPT ![self] = ntg]
                               ELSE /\ TRUE
                                    /\ UNCHANGED num_to_grab_gq
                         /\ LET grabbed_tasks == (CHOOSE t \in SUBSET gq: (Cardinality(t) = num_to_grab_gq'[self])) IN
                              IF grabbed_tasks = {}
                                 THEN /\ ret' = [ret EXCEPT ![self] = NULL]
                                      /\ pc' = [pc EXCEPT ![self] = "gfgl0"]
                                      /\ UNCHANGED << stack, tasks_ >>
                                 ELSE /\ LET single_task == CHOOSE t1 \in grabbed_tasks: TRUE IN
                                           /\ ret' = [ret EXCEPT ![self] = single_task]
                                           /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lq_put_bulk",
                                                                                       pc        |->  "gfgl0",
                                                                                       tasks_    |->  tasks_[self] ] >>
                                                                                   \o stack[self]]
                                              /\ tasks_' = [tasks_ EXCEPT ![self] = grabbed_tasks \ {single_task}]
                                           /\ pc' = [pc EXCEPT ![self] = "LqPutBulk"]
                    /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, 
                                    lq, idle, idle_count, spinning_count, 
                                    parking_slot, done, processes, slock, 
                                    epoch, p, task_, victim, tasks, localp_, 
                                    localtask, localp, curtask, task_p, lcnt, 
                                    task, maxtasksl, epoch_ >>

gfgl0(self) == /\ pc[self] = "gfgl0"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ num_to_grab_gq' = [num_to_grab_gq EXCEPT ![self] = Head(stack[self]).num_to_grab_gq]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                               ret, idle, idle_count, spinning_count, 
                               parking_slot, done, processes, slock, epoch, p, 
                               task_, tasks_, victim, tasks, localp_, 
                               localtask, localp, curtask, task_p, lcnt, task, 
                               maxtasksl, epoch_ >>

grab_from_gq(self) == GrabFromGq(self) \/ gfgl0(self)

TryFromGq(self) == /\ pc[self] = "TryFromGq"
                   /\ IF gq = {}
                         THEN /\ ret' = [ret EXCEPT ![self] = NULL]
                              /\ gq' = gq
                         ELSE /\ LET tftask == CHOOSE t \in gq: TRUE IN
                                   /\ gq' = gq \ {tftask}
                                   /\ ret' = [ret EXCEPT ![self] = tftask]
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << stopped, counter, signaled, lq_size, lq, 
                                   idle, idle_count, spinning_count, 
                                   parking_slot, done, processes, slock, epoch, 
                                   p, task_, tasks_, victim, tasks, 
                                   num_to_grab_gq, localp_, localtask, localp, 
                                   curtask, task_p, lcnt, task, maxtasksl, 
                                   epoch_ >>

try_from_gq(self) == TryFromGq(self)

TrySteal(self) == /\ pc[self] = "TrySteal"
                  /\ \E pts \in {ppts \in Ps: ppts /= self}:
                       localp_' = [localp_ EXCEPT ![self] = pts]
                  /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lq_steal",
                                                              pc        |->  "tsl0",
                                                              victim    |->  victim[self] ] >>
                                                          \o stack[self]]
                     /\ victim' = [victim EXCEPT ![self] = localp_'[self]]
                  /\ pc' = [pc EXCEPT ![self] = "LqSteal"]
                  /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                                  ret, idle, idle_count, spinning_count, 
                                  parking_slot, done, processes, slock, epoch, 
                                  p, task_, tasks_, tasks, num_to_grab_gq, 
                                  localtask, localp, curtask, task_p, lcnt, 
                                  task, maxtasksl, epoch_ >>

tsl0(self) == /\ pc[self] = "tsl0"
              /\ IF ret[self] = {}
                    THEN /\ ret' = [ret EXCEPT ![self] = NULL]
                         /\ pc' = [pc EXCEPT ![self] = "tsl2"]
                         /\ UNCHANGED << stack, tasks_, localtask >>
                    ELSE /\ LET tstask == CHOOSE t \in ret[self]: TRUE IN
                              localtask' = [localtask EXCEPT ![self] = tstask]
                         /\ ret' = [ret EXCEPT ![self] = ret[self] \ {localtask'[self]}]
                         /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lq_put_bulk",
                                                                     pc        |->  "tsl1",
                                                                     tasks_    |->  tasks_[self] ] >>
                                                                 \o stack[self]]
                            /\ tasks_' = [tasks_ EXCEPT ![self] = ret'[self]]
                         /\ pc' = [pc EXCEPT ![self] = "LqPutBulk"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, epoch, p, task_, victim, 
                              tasks, num_to_grab_gq, localp_, localp, curtask, 
                              task_p, lcnt, task, maxtasksl, epoch_ >>

tsl1(self) == /\ pc[self] = "tsl1"
              /\ ret' = [ret EXCEPT ![self] = localtask[self]]
              /\ pc' = [pc EXCEPT ![self] = "tsl2"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, stack, epoch, p, task_, 
                              tasks_, victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

tsl2(self) == /\ pc[self] = "tsl2"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ localp_' = [localp_ EXCEPT ![self] = Head(stack[self]).localp_]
              /\ localtask' = [localtask EXCEPT ![self] = Head(stack[self]).localtask]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp, curtask, 
                              task_p, lcnt, task, maxtasksl, epoch_ >>

try_steal(self) == TrySteal(self) \/ tsl0(self) \/ tsl1(self) \/ tsl2(self)

StartSpinning(self) == /\ pc[self] = "StartSpinning"
                       /\ IF spinning_count < (Cardinality(Ps) \div 2)
                             THEN /\ pc' = [pc EXCEPT ![self] = "IncSpin"]
                                  /\ ret' = ret
                             ELSE /\ ret' = [ret EXCEPT ![self] = FALSE]
                                  /\ pc' = [pc EXCEPT ![self] = "ssl1"]
                       /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, 
                                       lq, idle, idle_count, spinning_count, 
                                       parking_slot, done, processes, slock, 
                                       stack, epoch, p, task_, tasks_, victim, 
                                       tasks, num_to_grab_gq, localp_, 
                                       localtask, localp, curtask, task_p, 
                                       lcnt, task, maxtasksl, epoch_ >>

IncSpin(self) == /\ pc[self] = "IncSpin"
                 /\ spinning_count' = spinning_count + 1
                 /\ ret' = [ret EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "ssl1"]
                 /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                                 idle, idle_count, parking_slot, done, 
                                 processes, slock, stack, epoch, p, task_, 
                                 tasks_, victim, tasks, num_to_grab_gq, 
                                 localp_, localtask, localp, curtask, task_p, 
                                 lcnt, task, maxtasksl, epoch_ >>

ssl1(self) == /\ pc[self] = "ssl1"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

start_spinning(self) == StartSpinning(self) \/ IncSpin(self) \/ ssl1(self)

StopSpinning(self) == /\ pc[self] = "StopSpinning"
                      /\ Assert(spinning_count > 0, 
                                "Failure of assertion at line 185, column 1.")
                      /\ ret' = [ret EXCEPT ![self] = (spinning_count = 1)]
                      /\ spinning_count' = spinning_count - 1
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, 
                                      lq, idle, idle_count, parking_slot, done, 
                                      processes, slock, epoch, p, task_, 
                                      tasks_, victim, tasks, num_to_grab_gq, 
                                      localp_, localtask, localp, curtask, 
                                      task_p, lcnt, task, maxtasksl, epoch_ >>

stop_spinning(self) == StopSpinning(self)

AnouncePark(self) == /\ pc[self] = "AnouncePark"
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                              pc        |->  "apl0" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "Lock"]
                     /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, 
                                     lq, ret, idle, idle_count, spinning_count, 
                                     parking_slot, done, processes, slock, 
                                     epoch, p, task_, tasks_, victim, tasks, 
                                     num_to_grab_gq, localp_, localtask, 
                                     localp, curtask, task_p, lcnt, task, 
                                     maxtasksl, epoch_ >>

apl0(self) == /\ pc[self] = "apl0"
              /\ idle' = (idle \union {self})
              /\ pc' = [pc EXCEPT ![self] = "apl1"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle_count, spinning_count, parking_slot, done, 
                              processes, slock, stack, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

apl1(self) == /\ pc[self] = "apl1"
              /\ idle_count' = idle_count + 1
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                       pc        |->  Head(stack[self]).pc ] >>
                                                   \o Tail(stack[self])]
              /\ pc' = [pc EXCEPT ![self] = "Unlock"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, spinning_count, parking_slot, done, 
                              processes, slock, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

anounce_park(self) == AnouncePark(self) \/ apl0(self) \/ apl1(self)

AnounceUnpark(self) == /\ pc[self] = "AnounceUnpark"
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                                pc        |->  "aul0" ] >>
                                                            \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "Lock"]
                       /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, 
                                       lq, ret, idle, idle_count, 
                                       spinning_count, parking_slot, done, 
                                       processes, slock, epoch, p, task_, 
                                       tasks_, victim, tasks, num_to_grab_gq, 
                                       localp_, localtask, localp, curtask, 
                                       task_p, lcnt, task, maxtasksl, epoch_ >>

aul0(self) == /\ pc[self] = "aul0"
              /\ IF self \in idle
                    THEN /\ pc' = [pc EXCEPT ![self] = "aul1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "aul3"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, stack, epoch, p, task_, 
                              tasks_, victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

aul1(self) == /\ pc[self] = "aul1"
              /\ idle' = idle \ {self}
              /\ pc' = [pc EXCEPT ![self] = "aul2"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle_count, spinning_count, parking_slot, done, 
                              processes, slock, stack, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

aul2(self) == /\ pc[self] = "aul2"
              /\ idle_count' = idle_count - 1
              /\ pc' = [pc EXCEPT ![self] = "aul3"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, spinning_count, parking_slot, done, 
                              processes, slock, stack, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

aul3(self) == /\ pc[self] = "aul3"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                       pc        |->  Head(stack[self]).pc ] >>
                                                   \o Tail(stack[self])]
              /\ pc' = [pc EXCEPT ![self] = "Unlock"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

anounce_unpark(self) == AnounceUnpark(self) \/ aul0(self) \/ aul1(self)
                           \/ aul2(self) \/ aul3(self)

WakeWorker(self) == /\ pc[self] = "WakeWorker"
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                             pc        |->  "wwl0" ] >>
                                                         \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "Lock"]
                    /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, 
                                    lq, ret, idle, idle_count, spinning_count, 
                                    parking_slot, done, processes, slock, 
                                    epoch, p, task_, tasks_, victim, tasks, 
                                    num_to_grab_gq, localp_, localtask, localp, 
                                    curtask, task_p, lcnt, task, maxtasksl, 
                                    epoch_ >>

wwl0(self) == /\ pc[self] = "wwl0"
              /\ \E wwp \in idle:
                   localp' = [localp EXCEPT ![self] = wwp]
              /\ pc' = [pc EXCEPT ![self] = "wwl1"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, stack, epoch, p, task_, 
                              tasks_, victim, tasks, num_to_grab_gq, localp_, 
                              localtask, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

wwl1(self) == /\ pc[self] = "wwl1"
              /\ idle' = idle \ {localp[self]}
              /\ pc' = [pc EXCEPT ![self] = "wwl2"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle_count, spinning_count, parking_slot, done, 
                              processes, slock, stack, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

wwl2(self) == /\ pc[self] = "wwl2"
              /\ idle_count' = idle_count - 1
              /\ /\ p' = [p EXCEPT ![self] = p[self]]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_p",
                                                          pc        |->  "wwl3",
                                                          p         |->  p[self] ] >>
                                                      \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "WakeP"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, spinning_count, parking_slot, done, 
                              processes, slock, epoch, task_, tasks_, victim, 
                              tasks, num_to_grab_gq, localp_, localtask, 
                              localp, curtask, task_p, lcnt, task, maxtasksl, 
                              epoch_ >>

wwl3(self) == /\ pc[self] = "wwl3"
              /\ /\ localp' = [localp EXCEPT ![self] = Head(stack[self]).localp]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                          pc        |->  Head(stack[self]).pc ] >>
                                                      \o Tail(stack[self])]
              /\ pc' = [pc EXCEPT ![self] = "Unlock"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

wake_worker(self) == WakeWorker(self) \/ wwl0(self) \/ wwl1(self)
                        \/ wwl2(self) \/ wwl3(self)

TryPickTask(self) == /\ pc[self] = "TryPickTask"
                     /\ \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "try_from_gq",
                                                                    pc        |->  "tptl0_" ] >>
                                                                \o stack[self]]
                           /\ pc' = [pc EXCEPT ![self] = "TryFromGq"]
                        \/ /\ TRUE
                           /\ pc' = [pc EXCEPT ![self] = "tptl1_"]
                           /\ stack' = stack
                     /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, 
                                     lq, ret, idle, idle_count, spinning_count, 
                                     parking_slot, done, processes, slock, 
                                     epoch, p, task_, tasks_, victim, tasks, 
                                     num_to_grab_gq, localp_, localtask, 
                                     localp, curtask, task_p, lcnt, task, 
                                     maxtasksl, epoch_ >>

tptl0_(self) == /\ pc[self] = "tptl0_"
                /\ IF ret[self] /= NULL
                      THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ curtask' = [curtask EXCEPT ![self] = Head(stack[self]).curtask]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "tptl1_"]
                           /\ UNCHANGED << stack, curtask >>
                /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                                ret, idle, idle_count, spinning_count, 
                                parking_slot, done, processes, slock, epoch, p, 
                                task_, tasks_, victim, tasks, num_to_grab_gq, 
                                localp_, localtask, localp, task_p, lcnt, task, 
                                maxtasksl, epoch_ >>

tptl1_(self) == /\ pc[self] = "tptl1_"
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lq_get",
                                                         pc        |->  "tptl2" ] >>
                                                     \o stack[self]]
                /\ pc' = [pc EXCEPT ![self] = "LqGet"]
                /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                                ret, idle, idle_count, spinning_count, 
                                parking_slot, done, processes, slock, epoch, p, 
                                task_, tasks_, victim, tasks, num_to_grab_gq, 
                                localp_, localtask, localp, curtask, task_p, 
                                lcnt, task, maxtasksl, epoch_ >>

tptl2(self) == /\ pc[self] = "tptl2"
               /\ IF ret[self] /= NULL
                     THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ curtask' = [curtask EXCEPT ![self] = Head(stack[self]).curtask]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "tptl3"]
                          /\ UNCHANGED << stack, curtask >>
               /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                               ret, idle, idle_count, spinning_count, 
                               parking_slot, done, processes, slock, epoch, p, 
                               task_, tasks_, victim, tasks, num_to_grab_gq, 
                               localp_, localtask, localp, task_p, lcnt, task, 
                               maxtasksl, epoch_ >>

tptl3(self) == /\ pc[self] = "tptl3"
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "grab_from_gq",
                                                        pc        |->  "tptl4",
                                                        num_to_grab_gq |->  num_to_grab_gq[self] ] >>
                                                    \o stack[self]]
               /\ num_to_grab_gq' = [num_to_grab_gq EXCEPT ![self] = lq_size]
               /\ pc' = [pc EXCEPT ![self] = "GrabFromGq"]
               /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                               ret, idle, idle_count, spinning_count, 
                               parking_slot, done, processes, slock, epoch, p, 
                               task_, tasks_, victim, tasks, localp_, 
                               localtask, localp, curtask, task_p, lcnt, task, 
                               maxtasksl, epoch_ >>

tptl4(self) == /\ pc[self] = "tptl4"
               /\ IF ret[self] /= NULL
                     THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ curtask' = [curtask EXCEPT ![self] = Head(stack[self]).curtask]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "tptl5"]
                          /\ UNCHANGED << stack, curtask >>
               /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                               ret, idle, idle_count, spinning_count, 
                               parking_slot, done, processes, slock, epoch, p, 
                               task_, tasks_, victim, tasks, num_to_grab_gq, 
                               localp_, localtask, localp, task_p, lcnt, task, 
                               maxtasksl, epoch_ >>

tptl5(self) == /\ pc[self] = "tptl5"
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "start_spinning",
                                                        pc        |->  "tptl6" ] >>
                                                    \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "StartSpinning"]
               /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                               ret, idle, idle_count, spinning_count, 
                               parking_slot, done, processes, slock, epoch, p, 
                               task_, tasks_, victim, tasks, num_to_grab_gq, 
                               localp_, localtask, localp, curtask, task_p, 
                               lcnt, task, maxtasksl, epoch_ >>

tptl6(self) == /\ pc[self] = "tptl6"
               /\ IF ret[self]
                     THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "try_steal",
                                                                   pc        |->  "tptl7",
                                                                   localp_   |->  localp_[self],
                                                                   localtask |->  localtask[self] ] >>
                                                               \o stack[self]]
                          /\ localp_' = [localp_ EXCEPT ![self] = NULL]
                          /\ localtask' = [localtask EXCEPT ![self] = NULL]
                          /\ pc' = [pc EXCEPT ![self] = "TrySteal"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "tptl9"]
                          /\ UNCHANGED << stack, localp_, localtask >>
               /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                               ret, idle, idle_count, spinning_count, 
                               parking_slot, done, processes, slock, epoch, p, 
                               task_, tasks_, victim, tasks, num_to_grab_gq, 
                               localp, curtask, task_p, lcnt, task, maxtasksl, 
                               epoch_ >>

tptl7(self) == /\ pc[self] = "tptl7"
               /\ curtask' = [curtask EXCEPT ![self] = ret[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "stop_spinning",
                                                        pc        |->  "tptl8" ] >>
                                                    \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "StopSpinning"]
               /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                               ret, idle, idle_count, spinning_count, 
                               parking_slot, done, processes, slock, epoch, p, 
                               task_, tasks_, victim, tasks, num_to_grab_gq, 
                               localp_, localtask, localp, task_p, lcnt, task, 
                               maxtasksl, epoch_ >>

tptl8(self) == /\ pc[self] = "tptl8"
               /\ IF curtask[self] /= NULL /\ ret[self]
                     THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_worker",
                                                                   pc        |->  "tptl9",
                                                                   localp    |->  localp[self] ] >>
                                                               \o stack[self]]
                          /\ localp' = [localp EXCEPT ![self] = NULL]
                          /\ pc' = [pc EXCEPT ![self] = "WakeWorker"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "tptl9"]
                          /\ UNCHANGED << stack, localp >>
               /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                               ret, idle, idle_count, spinning_count, 
                               parking_slot, done, processes, slock, epoch, p, 
                               task_, tasks_, victim, tasks, num_to_grab_gq, 
                               localp_, localtask, curtask, task_p, lcnt, task, 
                               maxtasksl, epoch_ >>

tptl9(self) == /\ pc[self] = "tptl9"
               /\ ret' = [ret EXCEPT ![self] = curtask[self]]
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ curtask' = [curtask EXCEPT ![self] = Head(stack[self]).curtask]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                               idle, idle_count, spinning_count, parking_slot, 
                               done, processes, slock, epoch, p, task_, tasks_, 
                               victim, tasks, num_to_grab_gq, localp_, 
                               localtask, localp, task_p, lcnt, task, 
                               maxtasksl, epoch_ >>

try_pick_task(self) == TryPickTask(self) \/ tptl0_(self) \/ tptl1_(self)
                          \/ tptl2(self) \/ tptl3(self) \/ tptl4(self)
                          \/ tptl5(self) \/ tptl6(self) \/ tptl7(self)
                          \/ tptl8(self) \/ tptl9(self)

TryPickTaskBeforePark(self) == /\ pc[self] = "TryPickTaskBeforePark"
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "try_from_gq",
                                                                        pc        |->  "tptl0" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "TryFromGq"]
                               /\ UNCHANGED << stopped, counter, gq, signaled, 
                                               lq_size, lq, ret, idle, 
                                               idle_count, spinning_count, 
                                               parking_slot, done, processes, 
                                               slock, epoch, p, task_, tasks_, 
                                               victim, tasks, num_to_grab_gq, 
                                               localp_, localtask, localp, 
                                               curtask, task_p, lcnt, task, 
                                               maxtasksl, epoch_ >>

tptl0(self) == /\ pc[self] = "tptl0"
               /\ IF ret[self] /= NULL
                     THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "tptl1"]
                          /\ stack' = stack
               /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                               ret, idle, idle_count, spinning_count, 
                               parking_slot, done, processes, slock, epoch, p, 
                               task_, tasks_, victim, tasks, num_to_grab_gq, 
                               localp_, localtask, localp, curtask, task_p, 
                               lcnt, task, maxtasksl, epoch_ >>

tptl1(self) == /\ pc[self] = "tptl1"
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "try_steal",
                                                        pc        |->  Head(stack[self]).pc,
                                                        localp_   |->  localp_[self],
                                                        localtask |->  localtask[self] ] >>
                                                    \o Tail(stack[self])]
               /\ localp_' = [localp_ EXCEPT ![self] = NULL]
               /\ localtask' = [localtask EXCEPT ![self] = NULL]
               /\ pc' = [pc EXCEPT ![self] = "TrySteal"]
               /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                               ret, idle, idle_count, spinning_count, 
                               parking_slot, done, processes, slock, epoch, p, 
                               task_, tasks_, victim, tasks, num_to_grab_gq, 
                               localp, curtask, task_p, lcnt, task, maxtasksl, 
                               epoch_ >>

try_pick_task_before_park(self) == TryPickTaskBeforePark(self)
                                      \/ tptl0(self) \/ tptl1(self)

SignalTask(self) == /\ pc[self] = "SignalTask"
                    /\ IF spinning_count = 0 /\ idle_count > 0
                          THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_worker",
                                                                        pc        |->  "stl0",
                                                                        localp    |->  localp[self] ] >>
                                                                    \o stack[self]]
                               /\ localp' = [localp EXCEPT ![self] = NULL]
                               /\ pc' = [pc EXCEPT ![self] = "WakeWorker"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "stl0"]
                               /\ UNCHANGED << stack, localp >>
                    /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, 
                                    lq, ret, idle, idle_count, spinning_count, 
                                    parking_slot, done, processes, slock, 
                                    epoch, p, task_, tasks_, victim, tasks, 
                                    num_to_grab_gq, localp_, localtask, 
                                    curtask, task_p, lcnt, task, maxtasksl, 
                                    epoch_ >>

stl0(self) == /\ pc[self] = "stl0"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

signal_task(self) == SignalTask(self) \/ stl0(self)

ptl0(self) == /\ pc[self] = "ptl0"
              /\ Assert(task_p[self] \in Nat, 
                        "Failure of assertion at line 276, column 1.")
              /\ \/ /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "gq_put",
                                                                pc        |->  "tpl3",
                                                                tasks     |->  tasks[self] ] >>
                                                            \o stack[self]]
                       /\ tasks' = [tasks EXCEPT ![self] = {task_p[self]}]
                    /\ pc' = [pc EXCEPT ![self] = "GqPut"]
                    /\ task_' = task_
                 \/ /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lq_put",
                                                                pc        |->  "ptl1",
                                                                task_     |->  task_[self] ] >>
                                                            \o stack[self]]
                       /\ task_' = [task_ EXCEPT ![self] = task_p[self]]
                    /\ pc' = [pc EXCEPT ![self] = "LqPut"]
                    /\ tasks' = tasks
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, epoch, p, tasks_, victim, 
                              num_to_grab_gq, localp_, localtask, localp, 
                              curtask, task_p, lcnt, task, maxtasksl, epoch_ >>

ptl1(self) == /\ pc[self] = "ptl1"
              /\ IF ret[self] /= TRUE
                    THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lq_steal",
                                                                     pc        |->  "ptl2",
                                                                     victim    |->  victim[self] ] >>
                                                                 \o stack[self]]
                            /\ victim' = [victim EXCEPT ![self] = self]
                         /\ pc' = [pc EXCEPT ![self] = "LqSteal"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "tpl3"]
                         /\ UNCHANGED << stack, victim >>
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, epoch, p, task_, tasks_, 
                              tasks, num_to_grab_gq, localp_, localtask, 
                              localp, curtask, task_p, lcnt, task, maxtasksl, 
                              epoch_ >>

ptl2(self) == /\ pc[self] = "ptl2"
              /\ ret' = [ret EXCEPT ![self] = ret[self] \union {task_p[self]}]
              /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "gq_put",
                                                          pc        |->  "tpl3",
                                                          tasks     |->  tasks[self] ] >>
                                                      \o stack[self]]
                 /\ tasks' = [tasks EXCEPT ![self] = ret'[self]]
              /\ pc' = [pc EXCEPT ![self] = "GqPut"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, epoch, p, task_, tasks_, 
                              victim, num_to_grab_gq, localp_, localtask, 
                              localp, curtask, task_p, lcnt, task, maxtasksl, 
                              epoch_ >>

tpl3(self) == /\ pc[self] = "tpl3"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ task_p' = [task_p EXCEPT ![self] = Head(stack[self]).task_p]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, lcnt, task, 
                              maxtasksl, epoch_ >>

put_task(self) == ptl0(self) \/ ptl1(self) \/ ptl2(self) \/ tpl3(self)

PushTask(self) == /\ pc[self] = "PushTask"
                  /\ IF stopped \/ counter > maxcounter
                        THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ lcnt' = [lcnt EXCEPT ![self] = Head(stack[self]).lcnt]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "tpl4"]
                             /\ UNCHANGED << stack, lcnt >>
                  /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                                  ret, idle, idle_count, spinning_count, 
                                  parking_slot, done, processes, slock, epoch, 
                                  p, task_, tasks_, victim, tasks, 
                                  num_to_grab_gq, localp_, localtask, localp, 
                                  curtask, task_p, task, maxtasksl, epoch_ >>

tpl4(self) == /\ pc[self] = "tpl4"
              /\ counter' = counter + 1
              /\ lcnt' = [lcnt EXCEPT ![self] = counter']
              /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "put_task",
                                                          pc        |->  "Signal",
                                                          task_p    |->  task_p[self] ] >>
                                                      \o stack[self]]
                 /\ task_p' = [task_p EXCEPT ![self] = lcnt'[self]]
              /\ pc' = [pc EXCEPT ![self] = "ptl0"]
              /\ UNCHANGED << stopped, gq, signaled, lq_size, lq, ret, idle, 
                              idle_count, spinning_count, parking_slot, done, 
                              processes, slock, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task, maxtasksl, 
                              epoch_ >>

Signal(self) == /\ pc[self] = "Signal"
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "signal_task",
                                                         pc        |->  "tpl5" ] >>
                                                     \o stack[self]]
                /\ pc' = [pc EXCEPT ![self] = "SignalTask"]
                /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                                ret, idle, idle_count, spinning_count, 
                                parking_slot, done, processes, slock, epoch, p, 
                                task_, tasks_, victim, tasks, num_to_grab_gq, 
                                localp_, localtask, localp, curtask, task_p, 
                                lcnt, task, maxtasksl, epoch_ >>

tpl5(self) == /\ pc[self] = "tpl5"
              /\ signaled' = (signaled \union {lcnt[self]})
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ lcnt' = [lcnt EXCEPT ![self] = Head(stack[self]).lcnt]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << stopped, counter, gq, lq_size, lq, ret, idle, 
                              idle_count, spinning_count, parking_slot, done, 
                              processes, slock, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, task, 
                              maxtasksl, epoch_ >>

push_task(self) == PushTask(self) \/ tpl4(self) \/ Signal(self)
                      \/ tpl5(self)

RunTask(self) == /\ pc[self] = "RunTask"
                 /\ done' = (done \union {task[self]})
                 /\ \E numtasks \in 0..maxtasks:
                      maxtasksl' = [maxtasksl EXCEPT ![self] = numtasks]
                 /\ pc' = [pc EXCEPT ![self] = "pushtask"]
                 /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                                 ret, idle, idle_count, spinning_count, 
                                 parking_slot, processes, slock, stack, epoch, 
                                 p, task_, tasks_, victim, tasks, 
                                 num_to_grab_gq, localp_, localtask, localp, 
                                 curtask, task_p, lcnt, task, epoch_ >>

pushtask(self) == /\ pc[self] = "pushtask"
                  /\ IF maxtasksl[self] > 0
                        THEN /\ maxtasksl' = [maxtasksl EXCEPT ![self] = maxtasksl[self] - 1]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "push_task",
                                                                      pc        |->  "pushtask",
                                                                      lcnt      |->  lcnt[self] ] >>
                                                                  \o stack[self]]
                             /\ lcnt' = [lcnt EXCEPT ![self] = 0]
                             /\ pc' = [pc EXCEPT ![self] = "PushTask"]
                             /\ task' = task
                        ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ maxtasksl' = [maxtasksl EXCEPT ![self] = Head(stack[self]).maxtasksl]
                             /\ task' = [task EXCEPT ![self] = Head(stack[self]).task]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ lcnt' = lcnt
                  /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                                  ret, idle, idle_count, spinning_count, 
                                  parking_slot, done, processes, slock, epoch, 
                                  p, task_, tasks_, victim, tasks, 
                                  num_to_grab_gq, localp_, localtask, localp, 
                                  curtask, task_p, epoch_ >>

run_task(self) == RunTask(self) \/ pushtask(self)

RunLoop(self) == /\ pc[self] = "RunLoop"
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "try_pick_task",
                                                          pc        |->  "rll0",
                                                          curtask   |->  curtask[self] ] >>
                                                      \o stack[self]]
                 /\ curtask' = [curtask EXCEPT ![self] = NULL]
                 /\ pc' = [pc EXCEPT ![self] = "TryPickTask"]
                 /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, 
                                 ret, idle, idle_count, spinning_count, 
                                 parking_slot, done, processes, slock, epoch, 
                                 p, task_, tasks_, victim, tasks, 
                                 num_to_grab_gq, localp_, localtask, localp, 
                                 task_p, lcnt, task, maxtasksl, epoch_ >>

rll0(self) == /\ pc[self] = "rll0"
              /\ IF ret[self] /= NULL
                    THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "run_task",
                                                                     pc        |->  "RunLoop",
                                                                     maxtasksl |->  maxtasksl[self],
                                                                     task      |->  task[self] ] >>
                                                                 \o stack[self]]
                            /\ task' = [task EXCEPT ![self] = ret[self]]
                         /\ maxtasksl' = [maxtasksl EXCEPT ![self] = 0]
                         /\ pc' = [pc EXCEPT ![self] = "RunTask"]
                    ELSE /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "prepare_park",
                                                                  pc        |->  "rll1" ] >>
                                                              \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "PreparePark"]
                         /\ UNCHANGED << task, maxtasksl >>
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, epoch_ >>

rll1(self) == /\ pc[self] = "rll1"
              /\ epoch_' = [epoch_ EXCEPT ![self] = ret[self]]
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "anounce_park",
                                                       pc        |->  "rll2" ] >>
                                                   \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "AnouncePark"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl >>

rll2(self) == /\ pc[self] = "rll2"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "try_pick_task_before_park",
                                                       pc        |->  "rll3" ] >>
                                                   \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "TryPickTaskBeforePark"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

rll3(self) == /\ pc[self] = "rll3"
              /\ IF ret[self] /= NULL
                    THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "anounce_unpark",
                                                                  pc        |->  "rll4" ] >>
                                                              \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "AnounceUnpark"]
                         /\ epoch' = epoch
                    ELSE /\ /\ epoch' = [epoch EXCEPT ![self] = epoch_[self]]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "park_on",
                                                                     pc        |->  "rll6",
                                                                     epoch     |->  epoch[self] ] >>
                                                                 \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "ParkOn"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, p, task_, tasks_, victim, 
                              tasks, num_to_grab_gq, localp_, localtask, 
                              localp, curtask, task_p, lcnt, task, maxtasksl, 
                              epoch_ >>

rll4(self) == /\ pc[self] = "rll4"
              /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "run_task",
                                                          pc        |->  "rll5",
                                                          maxtasksl |->  maxtasksl[self],
                                                          task      |->  task[self] ] >>
                                                      \o stack[self]]
                 /\ task' = [task EXCEPT ![self] = ret[self]]
              /\ maxtasksl' = [maxtasksl EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "RunTask"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, epoch, p, task_, tasks_, 
                              victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, epoch_ >>

rll5(self) == /\ pc[self] = "rll5"
              /\ pc' = [pc EXCEPT ![self] = "RunLoop"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, stack, epoch, p, task_, 
                              tasks_, victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

rll6(self) == /\ pc[self] = "rll6"
              /\ IF stopped
                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "rll7"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, stack, epoch, p, task_, 
                              tasks_, victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

rll7(self) == /\ pc[self] = "rll7"
              /\ pc' = [pc EXCEPT ![self] = "RunLoop"]
              /\ UNCHANGED << stopped, counter, gq, signaled, lq_size, lq, ret, 
                              idle, idle_count, spinning_count, parking_slot, 
                              done, processes, slock, stack, epoch, p, task_, 
                              tasks_, victim, tasks, num_to_grab_gq, localp_, 
                              localtask, localp, curtask, task_p, lcnt, task, 
                              maxtasksl, epoch_ >>

ps(self) == RunLoop(self) \/ rll0(self) \/ rll1(self) \/ rll2(self)
               \/ rll3(self) \/ rll4(self) \/ rll5(self) \/ rll6(self)
               \/ rll7(self)

Stopper == /\ pc["stopper"] = "Stopper"
           /\ (\A prs \in Ps: pc[prs] = "ParkOn" /\ lq[prs] = {}) /\ gq = {}
           /\ stopped' = TRUE
           /\ pc' = [pc EXCEPT !["stopper"] = "Done"]
           /\ UNCHANGED << counter, gq, signaled, lq_size, lq, ret, idle, 
                           idle_count, spinning_count, parking_slot, done, 
                           processes, slock, stack, epoch, p, task_, tasks_, 
                           victim, tasks, num_to_grab_gq, localp_, localtask, 
                           localp, curtask, task_p, lcnt, task, maxtasksl, 
                           epoch_ >>

stopper == Stopper

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == stopper
           \/ (\E self \in ProcSet:  \/ lock(self) \/ unlock(self)
                                     \/ prepare_park(self) \/ park_on(self)
                                     \/ wake_p(self) \/ lq_put(self)
                                     \/ lq_put_bulk(self) \/ lq_get(self)
                                     \/ lq_steal(self) \/ gq_put(self)
                                     \/ grab_from_gq(self) \/ try_from_gq(self)
                                     \/ try_steal(self) \/ start_spinning(self)
                                     \/ stop_spinning(self) \/ anounce_park(self)
                                     \/ anounce_unpark(self) \/ wake_worker(self)
                                     \/ try_pick_task(self)
                                     \/ try_pick_task_before_park(self)
                                     \/ signal_task(self) \/ put_task(self)
                                     \/ push_task(self) \/ run_task(self))
           \/ (\E self \in Ps: ps(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Ps : /\ WF_vars(ps(self))
                            /\ WF_vars(try_pick_task(self))
                            /\ WF_vars(run_task(self))
                            /\ WF_vars(prepare_park(self))
                            /\ WF_vars(anounce_park(self))
                            /\ WF_vars(try_pick_task_before_park(self))
                            /\ WF_vars(anounce_unpark(self))
                            /\ WF_vars(park_on(self))
                            /\ WF_vars(lock(self))
                            /\ WF_vars(unlock(self))
                            /\ WF_vars(wake_p(self))
                            /\ WF_vars(lq_put_bulk(self))
                            /\ WF_vars(lq_get(self))
                            /\ WF_vars(lq_steal(self))
                            /\ WF_vars(grab_from_gq(self))
                            /\ WF_vars(try_from_gq(self))
                            /\ WF_vars(try_steal(self))
                            /\ WF_vars(start_spinning(self))
                            /\ WF_vars(stop_spinning(self))
                            /\ WF_vars(wake_worker(self))
                            /\ WF_vars(lq_put(self))
                            /\ WF_vars(gq_put(self))
                            /\ WF_vars(signal_task(self))
                            /\ WF_vars(put_task(self))
                            /\ WF_vars(push_task(self))
        /\ SF_vars(stopper)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* TODO better

TypeOk ==
    /\ counter \in Nat
    /\ lq_size = 4
    /\ idle_count \in Nat
    /\ spinning_count \in Nat
    /\ slock \in {0, 1}
    /\ \A gqtask \in gq: gqtask \in Nat
    /\ \A prcs \in Ps: \A lqtask \in lq[prcs]: lqtask \in Nat

    
taskvars == <<counter,  lq_size, p, task_, localp_, 
           localtask, localp, curtask, task_p, lcnt, task, maxtasksl
        >>
        
setvars == <<gq, signaled, done, p, tasks_, tasks, num_to_grab_gq, localp_, localp
        >>

TcH == 
    /\ \A tidx \in DOMAIN taskvars: taskvars[tidx] = defaultInitValue /\ taskvars[tidx] \in Nat
    /\ \A tsetidx \in DOMAIN setvars: \A setelem \in setvars[tsetidx]: setelem = defaultInitValue /\ setelem \in Nat

Asserts ==
    /\ \A ppp \in Ps: Cardinality(lq[ppp]) <= lq_size

isIdle(prcs) ==  pc[prcs] = "ParkOn"

\* LoadBalance == 
    
SpilledTasks == idle /= Ps \/ Cardinality(done) = counter



=================================
