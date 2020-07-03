/*
This module is an analog to the InnerFIFO defined in
Specifying Systems(SS from now on) Chapter 3. I haven't
explored methods of interface/module hiding in Alloy, to
see if it's possible.
*/

//Generic, like the Channel module:
module FIFO[Data]

open Channel[Data]

sig Queue {
    inChan: one Channel,
    outChan: one Channel,
    buffer: (Data lone -> Time)->Time
}{
    inChan != outChan
}

//Making a top level send is equivalent to 
//the Send predicate for the queue's in channel:
pred Send[q: Queue, d: Data, t, t': Time] {
    //Preconditions:
    Channel/Send[q.inChan, d, t, t']
    //Postconditions:
    q.buffer.t' = q.buffer.t
    Channel/Stutter[q.outChan, t, t']
}

//This receives from the in channel and adds a 
//relation from the data to the time received to the
//buffer.
pred BufferReceive[q: Queue, d: Data, t, t': Time] {
    //Preconditions:
    Channel/Receive[q.inChan, d, t, t']
    //Postconditions:
    q.buffer.t' = q.buffer.t + d->t'
    Channel/Stutter[q.outChan, t, t']
}

//If the buffer is non-empty, take the oldest 
//relation in the buffer and send it to the out
//channel:
pred BufferSend[q: Queue, d: Data, t, t': Time] {
    //Preconditions:
    some q.buffer.t
    let firstItem = Head[q, t] {
        Channel/Send[q.outChan, d, t, t']
        //Postconditions:
        q.buffer.t' = q.buffer.t - firstItem
    }
    Channel/Stutter[q.inChan, t, t']
}

//Receives the item from the out channel:
pred Receive[q: Queue, d: Data, t, t': Time] {
    Channel/Receive[q.outChan, d, t, t']
    q.buffer.t' = q.buffer.t
    Channel/Stutter[q.inChan, t, t']
}

pred Stutter[q: Queue, t, t': Time] {
    q.buffer.t' = q.buffer.t
    Channel/Stutter[q.inChan, t, t']
    Channel/Stutter[q.outChan, t, t']
}

//Initially, there should be at least one queue, with 
//all buffers are empty and channels initialized.
pred Init[t: Time] {
    some Queue
    no buffer.t
    Channel/Init[t]
}

//For a specific time atom, retrieves the relation
//in the buffer with the earliest time, to ensure
//FIFO:
fun Head[q: Queue, t: Time]: Data->Time {
    let firstTime = min[q.buffer.t[Data]] |
    { d: Data, t': Time | t' = firstTime and d->t' in q.buffer.t }
}

//The trace idiom implementation, defining valid
//operations per step:
pred Trace {
    this/Init[first]
    all q: Queue, t: Time - last |
        let t' = t.next {
        Stutter[q, t, t'] or
        some d: Data {
            Send[q, d, t, t'] or
            BufferReceive[q, d, t, t'] or
            BufferSend[q, d, t, t'] or
            Receive[q, d, t, t']
        }
    }
}

run Trace for 2 but 12 Time

//TODO: Implement send and receive histories, to
//test that the FIFO property holds for sends
//and receives.