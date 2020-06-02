
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
        lock = w->t'
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
        w.lock = t
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

pred Init[t: Time] {
    no log.t
    no items.t
    no lock.t
    some Data
    some Writer
}

pred Trace {
    Init[first]
    all w: Writer, i: Data, t: Time - last {
        let t' = t.next |
            StartAdd[w, i, t, t'] or
            CommitAdd[w, i, t, t'] or
            Stutter[t, t']
    }
}

run Trace for 3 but 2 Writer, 10 Time
