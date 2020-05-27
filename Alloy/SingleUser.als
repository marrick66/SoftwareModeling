module SingleUser

//Alloy's method for evolution over time:
open util/ordering[Time]
sig Time {}

//A model of a single user
//that contains a set of generic
//data items over time:
sig Item {}
one sig User {
    data: Item->Time
}

//Database operations to 
//add and delete data items.
//Since DBOperation is abstract,
//AddOperation and DeleteOperation
//are the entirety of the set of operations.
//Dirty and Committed represent the state of 
//whether the log has updated the user:
abstract sig DBOperation {}
one sig AddOperation extends DBOperation {}
one sig DeleteOperation extends DBOperation {}

abstract sig LogState {}
one sig Dirty extends LogState {}
one sig Committed extends LogState {}

//A single database containing a log of
//operations over time for the user.
//Each time step can have at most one operation,
//so concurrency is not defined:
one sig Database {
    log: (DBOperation->Item->LogState) lone->Time
}

//For the initial state, both
//the data items and log are empty:
pred Init[t: Time] {
    no log.t
    no data.t
}