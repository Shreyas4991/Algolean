/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.ModelM

/-!
# A stateful query type for Singly Linked Lists

The query type `SinglyLinkedList α` models the abstract interface
for a singly linked list. Its basic interface is identical
to that of it's functional programming cousin, a recursively defined
list.
-/

@[expose] public section

namespace Algolean.Algorithms

/--
A state type with a single list that is used to internally
represent linear data structures like linked lists,
stacks, and queues.
-/
structure ListState (α : Type u) where
  /-- The internal list -/
  internalList : List α

/--
Insertion strategy. This can be either last-in-first-out (`lifo`)
or first-in-first-out (`fifo`)
-/
inductive Strategy where
  | lifo
  | fifo

/--
An ADT query type for a stack. Note this is essentially identical
to the List query type, but with renamed queries to match
the typical names of a stack interface.
-/
inductive ListADT (s : Strategy) (α : Type u) : Type u → Type u where
  | peek : ListADT s α (Option α)
  | drop : ListADT s α PUnit
  | insert (data : α) : ListADT s α PUnit

/--
A model for the stack query using the ListState to store
the stack internally in the state type.
-/
@[simps]
def listModel (s : Strategy) :
      ModelM (ListADT s α) (StateM (ListState α)) ℕ where
    evalQuery
      | .peek => do
            let iL ← get
            return (List.head? iL.internalList)
      | .drop => do
            let iL ← get
            set {internalList := List.tail iL.internalList : ListState α}
            return ()
      | .insert x => do
            match s with
            | .lifo => modify (fun iL => ⟨x :: iL.internalList⟩)
            | .fifo => modify (fun iL => ⟨iL.internalList ++ [x]⟩)
    cost _ := 1

/--
Interpretation of ListADT as the ADT of a stack
-/
abbrev stackModel {α} := @listModel α .lifo

/--
Interpretation of ListADT as the ADT of a queue
-/
abbrev queueModel {α} := @listModel α .fifo

end Algolean.Algorithms
