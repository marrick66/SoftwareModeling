----------------------------- MODULE SingleUser -----------------------------
EXTENDS Integers, Sequences, TLC

\* An attempt to model the database log and update of data
\* for a single user:
(*--algorithm SingleUser
variables
    items = { "item1", "item2", "item3", "item4" },
    user = [data |-> {}],
    log = <<>>,
    current_items \in (SUBSET items);

define
    \* Liveness property that for an item in
    \* the user's data, there is a dirty and committed entry(in that order).
    LogIsComplete(item) == \E x,y \in 1..Len(log): 
        /\ log[x].data = item 
        /\ log[y].data = item 
        /\ log[x].state = "Dirty" 
        /\ log[y].state = "Committed"
        /\ x < y
    \* Temporal formula stating that eventually, all items in the user's data
    \* are complete.
    AllItemsComplete == <>[](\A item \in user.data: LogIsComplete(item))

    \* Helper operation to get the most recent log state for
    \* an item.
    LastEntryStateIs(seq, item, state) ==
    LET matching == { x \in 1..Len(seq): seq[x].data = item } 
    IN seq = <<>> \/ (\E x \in matching: seq[x].state = state /\ \A y \in matching: x >= y)  

end define;

\* Using two concurrent processes:
fair process Log \in 1..2
    variables
        current_item \in current_items;
begin
    \* StartAdd verifies that the current item isn't already in the user's data,
    \* another add isn't in progress, and then writes a dirty record to the log.
    StartAdd:
        if current_item \notin user.data /\ LastEntryStateIs(log, current_item, "Committed") then
            log := Append(log, [ data |-> current_item, op |-> "Add", state |-> "Dirty"]);
        end if;

    \* CommitAdd checks to see if the current item isn't already in the user's data,
    \* there is an uncommitted dirty log entry, and then writes a commit entry to the 
    \* log and updates the user's data with the item. 
    CommitAdd:
        if current_item \notin user.data /\ LastEntryStateIs(log, current_item, "Dirty") then
            log := Append(log, [ data |-> current_item, op |-> "Add", state |-> "Committed"]);
            user := [data |-> user.data \union {current_item}];
        end if;
end process;
end algorithm; *)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-74c4053ecbccbf7b589afb589cdc520f
VARIABLES items, user, log, current_items, pc

(* define statement *)
LogIsComplete(item) == \E x,y \in 1..Len(log):
    /\ log[x].data = item
    /\ log[y].data = item
    /\ log[x].state = "Dirty"
    /\ log[y].state = "Committed"
    /\ x < y


AllItemsComplete == <>[](\A item \in user.data: LogIsComplete(item))



LastEntryStateIs(seq, item, state) ==
LET matching == { x \in 1..Len(seq): seq[x].data = item }
IN seq = <<>> \/ (\E x \in matching: seq[x].state = state /\ \A y \in matching: x >= y)

VARIABLE current_item

vars == << items, user, log, current_items, pc, current_item >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ items = { "item1", "item2", "item3", "item4" }
        /\ user = [data |-> {}]
        /\ log = <<>>
        /\ current_items \in (SUBSET items)
        (* Process Log *)
        /\ current_item \in [1..2 -> current_items]
        /\ pc = [self \in ProcSet |-> "StartAdd"]

StartAdd(self) == /\ pc[self] = "StartAdd"
                  /\ IF current_item[self] \notin user.data /\ LastEntryStateIs(log, current_item[self], "Committed")
                        THEN /\ log' = Append(log, [ data |-> current_item[self], op |-> "Add", state |-> "Dirty"])
                        ELSE /\ TRUE
                             /\ log' = log
                  /\ pc' = [pc EXCEPT ![self] = "CommitAdd"]
                  /\ UNCHANGED << items, user, current_items, current_item >>

CommitAdd(self) == /\ pc[self] = "CommitAdd"
                   /\ IF current_item[self] \notin user.data /\ LastEntryStateIs(log, current_item[self], "Dirty")
                         THEN /\ log' = Append(log, [ data |-> current_item[self], op |-> "Add", state |-> "Committed"])
                              /\ user' = [data |-> user.data \union {current_item[self]}]
                         ELSE /\ TRUE
                              /\ UNCHANGED << user, log >>
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << items, current_items, current_item >>

Log(self) == StartAdd(self) \/ CommitAdd(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: Log(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..2 : WF_vars(Log(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-603a6deeb0a98bf92767ae64063c4342
=============================================================================
\* Modification History
\* Last modified Wed May 27 13:38:25 CDT 2020 by Sean.Mayfield
\* Created Tue May 26 14:09:19 CDT 2020 by Sean.Mayfield
