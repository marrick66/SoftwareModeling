/*
This module is an analog to the Channel defined in
Specifying Systems(SS from now on) Chapter 3, with Alloy specific
modifications along the way.
*/

//Generic to use any sort of data atom desired:
module Channel[Data]

open util/ordering[Time]

sig Time {}

//SS uses binary integers to represent
//the two states of the ready and ack lines.
//In this case, I thought an Alloy enum would
//be more appropriate.
abstract sig LineState {}
one sig Open extends LineState {}
one sig Closed extends LineState {}

//The channel implementation uses the tracing idiom,
//with each value of the signature associated with an 
//ordered time atom.
sig Channel {
    //Another alteration is instead of allowing
    //any value when ready and ack are in the same
    //state, it's empty to make things more explicit.
    //It's not essential to the spec, though.
    value: Data lone->Time,
    //ready and ack states are defined for
    //every time atom.
    ready: LineState one->Time,
    ack: LineState one->Time
}

//The send operation for a channel sets the value
//and flips the ready line:
pred Send[chan: Channel, d: Data, t, t': Time] {
    //Preconditions:
    no chan.value.t
    chan.ready.t = chan.ack.t
    //Postconditions:
    chan.ready.t' = Flip[chan.ready.t]
    chan.ack.t' = chan.ack.t
    chan.value.t' = d
}

//The receive operation for a data item clears
//the value and flips the ack line:
pred Receive[chan: Channel, d: Data, t, t': Time] {
    //Preconditions:
    chan.ready.t != chan.ack.t
    chan.value.t = d
    //Postconditions:
    chan.ack.t' = Flip[chan.ack.t]
    chan.ready.t' = chan.ready.t
    no chan.value.t' 
}

//The initial state for all channels is for
//the value to be empty with the ready and ack lines
//synchronized (doesn't matter to what value):
pred Init[t: Time] {
    no value.t
    ready.t = ack.t
}

//Obligatory stutter action, with the channel
//remaining in it's previous state.
pred Stutter[chan: Channel, t, t': Time] {
    chan.value.t' = chan.value.t
    chan.ready.t' = chan.ready.t
    chan.ack.t' = chan.ack.t
}

//The trace idiom implementation, which states that
//for each step, the channel can either send, receive,
//or do nothing:
pred Trace {
    Init[first]
    all t: Time - last |
        let t' = t.next |
            all chan: Channel |
                some d: Data |
                Send[chan, d, t, t'] or 
                Receive[chan, d, t, t'] or 
                Stutter[chan, t, t']

}

//This function simply takes a line state and
//returns what we define as opposite: Open->Closed,
//Closed->Open:
fun Flip(ls: LineState): LineState {
    { fs: LineState | 
        ls = Open implies fs = Closed 
        else fs = Open }
}

//A predicate used to compose an invariant that if
//the channel has no value, it's lines are synchronized.
//Also states the converse is true. 
pred ValidReceiveState {
    Trace implies
    all t: Time, chan: Channel {
        no chan.value.t implies chan.ready.t = chan.ack.t
        chan.ready.t = chan.ack.t implies no chan.value.t
    }

}

//A predicate used to compose an invariant that if
//the channel has a value, it's lines are not synchronized.
//Also states the converse is true. 
pred ValidSendState {
    Trace implies
    all t: Time, chan: Channel {
        some chan.value.t implies chan.ready.t != chan.ack.t
        chan.ready.t != chan.ack.t implies some chan.value.t
    }
}

//The invariants above where defined as predicates to allow
//inspection of trace values. Here, they're conjuncted to form
//the actual invariant to check.
assert ValidOperationStates {
    ValidSendState
    ValidReceiveState
}

check ValidOperationStates for 3 but 8 Time
run Trace for 3 but 8 Time