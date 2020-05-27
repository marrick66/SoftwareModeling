
open SingleUser

fun LastLogTime[i: Item, t: Time]: Time {
    let prevTimes = t.prevs & Database.log[DBOperation][i][LogState] |
	max[prevTimes]
}

//Predicate for writing a new log entry for an item.
//PRE:
//  a. The last log entry prior to t must be committed.
//POST:
//  a. A log entry of op->i->Dirty is set as the 
//  relation for t'.
pred WriteLogEntry[i: Item, op: DBOperation, t, t': Time] {
    let pre = LastLogTime[i, t] |
        no pre or
        Database.log[DBOperation][i].pre != Dirty
    Database.log.t' = op->i->Dirty
}

//Predicate for committing a dirty write to the log.
//PRE:
//  a. The last log entry prior to t must match the op parameter.
//  b. The last log entry prior to t must be Dirty.
//POST:
//  a. A log entry of op->i->Committed is set as the
//  relation for t'
pred CommitLogEntry[i: Item, op: DBOperation, t, t': Time] {
    let pre = LastLogTime[i, t] |
        Database.log[op][i].pre = Dirty
    Database.log.t' = op->i->Committed
}

//Predicate for the start of an add operation.
//PRE:
//  a. The item does not already exist in the data.
//  b. An add log entry can be written.
//POST:
//  a. The add log entry is written.
//  b. The data for the user is unchanged.
pred StartAdd[i: Item, t, t': Time] {
    i not in User.data.t
    WriteLogEntry[i, AddOperation, t, t']
    User.data.t' = User.data.t
}

//Predicate for committing an add operation.
//PRE:
//  a. A commit entry can be written.
//POST:
//  a. A commit entry is written.
//  b. The item added is inserted into the data set.
pred CompleteAdd[i: Item, t, t': Time] {
    i not in User.data.t
    CommitLogEntry[i, AddOperation, t, t']
    User.data.t' = User.data.t + i
}

//Predicate for a stutter or no change step.
pred NoChange[t, t': Time] {
    data.t' = data.t
    no log.t'
}

//Execution trace using interleaving operations
//across time units:
pred Trace {
    Init[first]
    all i: Item, t: Time - last |
        let t' = t.next |
        StartAdd[i, t, t'] or
        CompleteAdd[i, t, t'] or
        NoChange[t, t']
}

//Invariant that for every item in the user's data,
//there is a dirty write followed by a commit.
assert AllItemsComplete {
    all t: User.data[Item] |
    all i: User.data.t |
        some t', t'': (t + t.prevs) {
            lt[t', t'']
            Database.log[AddOperation][i].t' = Dirty
            Database.log[AddOperation][i].t'' = Committed
        }
}

fact Execution {
    Trace
}

check AllItemsComplete for 3 but 8 Time
