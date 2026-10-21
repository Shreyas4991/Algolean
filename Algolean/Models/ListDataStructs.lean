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
The query type for a singlylinkedlist
-/
inductive SinglyLinkedList (α : Type u) : Type u → Type u where
  | head : SinglyLinkedList α (Option α)
  | tail : SinglyLinkedList α PUnit
  | cons (newHead : α) : SinglyLinkedList α PUnit

/--
A stateful model for a singly linked list.
-/
@[simps]
def singlyLLModel : ModelM (SinglyLinkedList α) (StateM (ListState α)) ℕ where
    evalQuery
      | .head => do
            let iL ← get
            return (List.head? iL.internalList)
      | .tail => do
            let iL ← get
            set {internalList := List.tail iL.internalList : ListState α}
            return ()
      | .cons x => do
            modify (fun iL => ⟨x :: iL.internalList⟩)
    cost _ := 1

/--
An ADT query type for a stack. Note this is essentially identical
to the List query type, but with renamed queries to match
the typical names of a stack interface.
-/
inductive Stack (α : Type u) : Type u → Type u where
  | top : Stack α (Option α)
  | pop : Stack α PUnit
  | push (newHead : α) : Stack α PUnit

/--
A model for the stack query using the ListState to store
the stack internally in the state type.
-/
@[simps]
def stackModel : ModelM (Stack α) (StateM (ListState α)) ℕ where
    evalQuery
      | .top => do
            let iL ← get
            return (List.head? iL.internalList)
      | .pop => do
            let iL ← get
            set {internalList := List.tail iL.internalList : ListState α}
            return ()
      | .push x => do
            modify (fun iL => ⟨x :: iL.internalList⟩)
    cost _ := 1

/--
An ADT query type for a Queue.
-/
inductive Queue (α : Type u) : Type u → Type u where
  | front : Queue α (Option α)
  | pushback : Queue α PUnit
  | popfront (newHead : α) : Queue α PUnit

/--
A model for the queue query using the ListState to store
the stack internally in the state type.
-/
@[simps]
def queueModel : ModelM (Stack α) (StateM (ListState α)) ℕ where
    evalQuery
      | .top => do
            let iL ← get
            return (List.head? iL.internalList)
      | .pop => do
            let iL ← get
            set {internalList := List.tail iL.internalList : ListState α}
            return ()
      | .push x => do
            modify (fun iL => ⟨x :: iL.internalList⟩)
    cost _ := 1

end Algolean.Algorithms
