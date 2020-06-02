---- MODULE ConcurrentWriter ----
EXTENDS Integers, TLC, Sequences

CONSTANT WRITERS, ITEMS

(*--algorithm ConcurrentWriter
    variables
        selected_items \in SUBSET ITEMS,
        log = <<>>,
        entity = [lock |-> {}, data |-> {}],
        current_items = selected_items;
define
    \*Invariant stating that an item in the
    \*entity data set has a dirty followed by a
    \*committed log entry:
    ItemHasCompleteLogEntries(item) ==
        \E x,y \in 1..Len(log): 
            /\ x < y 
            /\ log[x].data = item 
            /\ log[x].state = "Dirty"
            /\ log[y].data = item 
            /\ log[y].state = "Committed"
    
    \*Invariant stating that all items contained
    \*in the entity have a complete log entry:
    AllEntityItemsHaveCommittedLog ==
        \A item \in entity.data: ItemHasCompleteLogEntries(item)
    
    \*Helper operation that gets the set of indexes in the log
    \*that contain an entry for the specified item:
    LastLogIndex(item) == 
        { index \in 1..Len(log): log[index].data = item }

    \*Helper operation predicate that states whether the 
    \*last log entry for an item has the specified state:
    LastLogEntryStateIs(item, state) ==
        LET matching == LastLogIndex(item)
        IN \E index1 \in matching: log[index1].state = state /\ \A index2 \in matching: index1 >= index2
    
    \*Liveness property that every item in the
    \*global sample set is eventually added to the entity:
    AllDataAdded == <>[](selected_items = entity.data)
            
end define;

macro add_to_log(item, itemState) begin
    log := Append(log, [data |-> item, op |-> "Add", state |-> itemState]);
end macro;

\*A writer process that attempts to add some
\*item that hasn't already been added until there
\*are none.
fair process Writer \in WRITERS
    variables
        in_proc_item = "";

begin EventLoop:
    while current_items /= {} do
        \*Choose an item, and with the following preconditions:
        \*  a. There is no lock held by a process.
        \*  b. The item hasn't already been added.
        \*  c. There is no log entry for the item.
        \*1. Acquire the lock on the entity.
        \*2. Store the current item locally.
        \*3. Add a dirty entry to the log for the item.
        StartAdd:
            with current_item \in current_items do
                if entity.lock = {} 
                    /\ LastLogIndex(current_item) = {}
                    /\ current_item \notin entity.data then
                        entity := [data |-> entity.data, lock |-> {self}];
                        in_proc_item := current_item;
                        add_to_log(current_item, "Dirty");
                end if;
            end with;
        \*Commit and update the item with the following preconditions:
        \*  a. There is an item already in process.
        \*  b. This process holds the lock.
        \*  c. The item hasn't miraculously appeared in the entity.
        \*  d. The last log entry for the item is the dirty one from StartAdd.
        \*1. Write the committed log entry for the item.
        \*2. Update the entity with the added item.
        \*3. Remove the item from the sample set.
        \*4. Release the lock. 
        CommitAdd:
            if in_proc_item /= ""
                /\ entity.lock = {self}
                /\ in_proc_item \notin entity.data
                /\ LastLogEntryStateIs(in_proc_item, "Dirty") then
                    add_to_log(in_proc_item, "Committed");
                    entity := [data |-> entity.data \union {in_proc_item}, lock |-> {}];
                    current_items := current_items \ {in_proc_item};
            end if;
    end while;
end process;
    
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-2d042bbc8bc546b67590d8394452e741
VARIABLES selected_items, log, entity, current_items, pc

(* define statement *)
ItemHasCompleteLogEntries(item) ==
    \E x,y \in 1..Len(log):
        /\ x < y
        /\ log[x].data = item
        /\ log[x].state = "Dirty"
        /\ log[y].data = item
        /\ log[y].state = "Committed"



AllEntityItemsHaveCommittedLog ==
    \A item \in entity.data: ItemHasCompleteLogEntries(item)



LastLogIndex(item) ==
    { index \in 1..Len(log): log[index].data = item }



LastLogEntryStateIs(item, state) ==
    LET matching == LastLogIndex(item)
    IN \E index1 \in matching: log[index1].state = state /\ \A index2 \in matching: index1 >= index2



AllDataAdded == <>[](selected_items = entity.data)

VARIABLE in_proc_item

vars == << selected_items, log, entity, current_items, pc, in_proc_item >>

ProcSet == (WRITERS)

Init == (* Global variables *)
        /\ selected_items \in SUBSET ITEMS
        /\ log = <<>>
        /\ entity = [lock |-> {}, data |-> {}]
        /\ current_items = selected_items
        (* Process Writer *)
        /\ in_proc_item = [self \in WRITERS |-> ""]
        /\ pc = [self \in ProcSet |-> "EventLoop"]

EventLoop(self) == /\ pc[self] = "EventLoop"
                   /\ IF current_items /= {}
                         THEN /\ pc' = [pc EXCEPT ![self] = "StartAdd"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << selected_items, log, entity, current_items, 
                                   in_proc_item >>

StartAdd(self) == /\ pc[self] = "StartAdd"
                  /\ \E current_item \in current_items:
                       IF entity.lock = {}
                           /\ LastLogIndex(current_item) = {}
                           /\ current_item \notin entity.data
                          THEN /\ entity' = [data |-> entity.data, lock |-> {self}]
                               /\ in_proc_item' = [in_proc_item EXCEPT ![self] = current_item]
                               /\ log' = Append(log, [data |-> current_item, op |-> "Add", state |-> "Dirty"])
                          ELSE /\ TRUE
                               /\ UNCHANGED << log, entity, in_proc_item >>
                  /\ pc' = [pc EXCEPT ![self] = "CommitAdd"]
                  /\ UNCHANGED << selected_items, current_items >>

CommitAdd(self) == /\ pc[self] = "CommitAdd"
                   /\ IF in_proc_item[self] /= ""
                          /\ entity.lock = {self}
                          /\ in_proc_item[self] \notin entity.data
                          /\ LastLogEntryStateIs(in_proc_item[self], "Dirty")
                         THEN /\ log' = Append(log, [data |-> in_proc_item[self], op |-> "Add", state |-> "Committed"])
                              /\ entity' = [data |-> entity.data \union {in_proc_item[self]}, lock |-> {}]
                              /\ current_items' = current_items \ {in_proc_item[self]}
                         ELSE /\ TRUE
                              /\ UNCHANGED << log, entity, current_items >>
                   /\ pc' = [pc EXCEPT ![self] = "EventLoop"]
                   /\ UNCHANGED << selected_items, in_proc_item >>

Writer(self) == EventLoop(self) \/ StartAdd(self) \/ CommitAdd(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in WRITERS: Writer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in WRITERS : WF_vars(Writer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-854a3059c6f9b3302bc9fad003419e00
====
