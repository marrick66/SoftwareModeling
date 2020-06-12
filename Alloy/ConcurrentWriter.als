
//Alloy's idomatic way of evolution of state 
//is an ordered sequence of time atoms:
open util/ordering[Time]
sig Time {}

//Generic atom representing some
//type of data.
sig Data {}

//Log operation enumerable. Right now,
//only implementing an add operation.
abstract sig LogOperation {}
one sig Add extends LogOperation {}

//Log entry state enumration when
//written to the log.
abstract sig LogEntryState {}
one sig Dirty extends LogEntryState {}
one sig Committed extends LogEntryState {}

//Represents some single entity that can be written to.
one sig Entity {
    //A relation that holds the set of data that
    //the entity contains at a point in time.
    items: Data->Time,
    //A relation for the log entries over time.
    //The lone multiplier indicates that only a single
    //log entry can be written for a point in time.
    log: (Data->LogOperation->LogEntryState) lone ->Time
}

//A writer can hold a single lock
//for a period of time. The relation tripped
//me up originally.
sig Writer {
    lock: set Time
}

//Since a writer's lock is held for a period
//of time, make sure that there is at most
//one lock held per time unit.
fact OnlyOneLockAtATime {
    all t: Time |
        lone log.t
}

//Begins the process of adding data by acquiring
//a lock and writing the dirty log entry.
pred StartAdd[w: Writer, d: Data, t, t': Time] {
    //Preconditions:
        //Lock is held:
        no lock.t
        //Data has not already been added:
        d not in Entity.items.t
        //No previous log entry was made:
        no LastLogEntry[d, t]
    //Postconditions:
        //Lock acquired:
        lock.t' = w
        //Log entry added:
        Entity.log.t' = d->Add->Dirty
    //Frame conditions:
        //Data remains unchanged:
        Entity.items.t' = Entity.items.t
}

//Finishes the add operation by writing the commit log entry,
//updating the entity's item set, and releasing the lock.
pred CommitAdd[w: Writer, d: Data, t, t': Time] {
    //Preconditions:
        //Data has not already been added:
        d not in Entity.items.t
        //The writer holds a lock:
        lock.t = w
        //The last log entry for the item is a dirty add:
        LastLogEntry[d, t] = Add->Dirty
    //Postconditions:
        //Write the committed log entry:
        Entity.log.t'[d] = Add->Committed
        //Update the entity's item set:
        Entity.items.t' = Entity.items.t + d
        //Release the lock:
        no lock.t'
}

//Represents a NoOp step. Locks and items remain
//unchanged, and no log entry exists.
pred Stutter[t, t': Time] {
    lock.t' = lock.t
    Entity.items.t' = Entity.items.t
    no log.t'
}

//Gets the last log entry for the data item starting from a particular
//time unit (inclusive).
fun LastLogEntry[d: Data, t: Time]: LogOperation->LogEntryState {
    let validIndexes = t + t.prevs |
    let lastEntryIndex = max[Entity.log[d][LogOperation][LogEntryState] & validIndexes] |
        Entity.log.lastEntryIndex[d]
}

//Initally, there should be no items in the state.
pred Init[t: Time] {
    no log.t
    no items.t
    no lock.t
    some Data
    some Writer
}

//Definition of possible operations over time. Defined
//as a predicate so it can be run to view instances.
pred Trace {
    Init[first]
    all t: Time - last {
        some w: Writer, i: Data |
        let t' = t.next |
            StartAdd[w, i, t, t'] or 
            CommitAdd[w, i, t, t'] or
            Stutter[t, t']
    }
}

//Prevents any stuttering if an operation can
//be performed. This is a hack, since stuttering is a valid
//execution state.
fact IfPossibleMakeProgress {
    all i: Data, t: Time |
        let t' = t.next |
        i not in Entity.items.t implies not Stutter[t, t']
}

//Trace set as a fact to allow checking of invariants.
fact Execution {
    Trace
}

//Invariant that states if a log entry exists at a
//unit of time, it must be due to a StartAdd or CommitAdd
//operation.
assert NoLogWrittenExceptOnOperation {
    all t: Time | 
    all e: Entity.log.t |
        let d = e.LogEntryState.LogOperation |
        let s = e[d][Add] |
        some w: Writer {
            s = Dirty implies StartAdd[w, d, t.prev, t]
            s = Committed implies CommitAdd[w, d, t.prev, t]
        }
}

//Invariant that states that the first time items
//have been added to the entity, there must be
//corresponding CommitAdd and single StartAdd operations.
assert AllDataAddedIsaResultOfOperations {
    all t: Time |
    let t' = t.next |
    all i: Entity.items.t' - Entity.items.t {
        some w:Writer |
        one st: t'.prevs |
        let st' = st.next {
            StartAdd[w, i, st, st']
            CommitAdd[w, i, t, t']
        }
    }
}

//This is a temporal property that isn't handled easily
//by Alloy due to bounded checking. A finite trace can 
//stutter until the bound. There are some methods for 
//tracing that ensure that there is a "back loop" that
//emulates an infinite trace by ensuring that all future
//states equal what has already been seen.
assert AllDataAddedEventually {
    some t: Time | Entity.items.t = Data
}

check NoLogWrittenExceptOnOperation for 3 but 10 Time
check AllDataAddedIsaResultOfOperations for 3 but 10 Time
check AllDataAddedEventually for 3 but 10 Time
run {} for 3 but 10 Time