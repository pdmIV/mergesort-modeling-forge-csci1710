#lang forge
option run_sterling "layout.cnd"

sig State {}

sig IntNode {
    value: one Int,
    next: pfunc State -> IntNode 
}

one sig LinkedList {
    head: pfunc State -> IntNode,
    firstState: one State,
    nextState: pfunc State -> State
}

//set comprehension to map State to State through LinkedList
fun state_pair[s1,s2:State]: set (State -> State) {
  {s1,s2: State | LinkedList.nextState[s1] = s2}
}

//set comprehension to map IntNode to IntNode over states
fun edges[s: State]: set (IntNode -> IntNode) {
  {i, j: IntNode | i.next[s] = j}
}

//For visual clarity and to make the problem more interesting, we are forcing all nodes to be unique
pred distinctValues { 
  all disj a, b: IntNode | a.value != b.value
}


--------------------------------------------------------------------------------------

pred wellformed {
  all s: State| {LinkedList.nextState[s] != s}
  all i: IntNode - LinkedList.head[LinkedList.firstState] | {not reachable[LinkedList.head[LinkedList.firstState],i,edges[LinkedList.firstState]]}
  all i: IntNode, s: State | {i.next[s] != i and i.next[s].next[s] != i and not reachable[i,i,edges[s]]}
  all disj s, s2: State {
    all l: LinkedList, i1,i2: IntNode | {
      distinctValues
      
      //all states have to come after first state and no state can map back to first state
      s != l.firstState implies {reachable[s,l.firstState,state_pair[s,s2]]}
      l.nextState[l.firstState] != none // just need to force a second state to exist
      l.nextState[s] != l.firstState and l.nextState[s2] != l.firstState
      l.nextState[s] != l.nextState[s2] and l.nextState[s] != s
      

      sorted[l.firstState]

      // acyclic
      not reachable[i1, i1, edges[s]]
      // head is not reachable through any node
      i1 != l.head[s] implies not reachable[l.head[s], i1, edges[s]]
      i2 = i1.next[s] implies {no i3: IntNode | {i3 != i1 and i2 = i3.next[s]}}


      // all nodes are reachable from head
      i1 != l.head[s] and s != l.firstState implies reachable[i1,l.head[s],edges[s]]

      //there must exist some detached node
      s = l.firstState implies {one i : IntNode | not reachable[i,l.head[s],edges[s]] and i!= l.head[s]}
    }
  }
}


//checks that all successive nodes are strictly increasing
pred sorted[s:State] {
  all i1,i2: IntNode|
      i1.next[s] = i2 implies i1.value < i2.value
}

//adding the new node into our linked list
pred newInsertion {
  let s = LinkedList.firstState | {
    let nx = LinkedList.nextState[s] {
      some nx
      some newNode: IntNode {
        not reachable[newNode, LinkedList.head[s], edges[s]]
        newNode != LinkedList.head[s]

        //must exist some node at the end with no next
        one tail: IntNode | {
          reachable[tail, LinkedList.head[s], edges[s]]
          no tail.next[s]
          tail.next[nx] = newNode
          no newNode.next[nx]


          //this line is just for testing purposes  -> forces the new node to have a smaller value than the head
          // newNode.value < LinkedList.head[LinkedList.firstState].value

          //frame conditions for new node
          all n: IntNode - tail - newNode | n.next[nx] = n.next[s]
        }
      }
    }
  }
}


pred swapping {
  all s: State - (LinkedList.firstState) | {  
    some LinkedList.nextState[s] implies {
      not sorted[s] implies {
        one i: IntNode | {
          //swapping position and pointers of the two nodes
          some i.next[s]
          i.next[s].value < i.value
          i.next[LinkedList.nextState[s]] = i.next[s].next[s]
          i.next[s].next[LinkedList.nextState[s]] = i

          i = LinkedList.head[s] implies {
            //predicate to handle the case where the head has to swap with another node
            i.next[s] = LinkedList.head[LinkedList.nextState[s]]

            //frame condition
            all n: IntNode - (i + i.next[s]) | n.next[LinkedList.nextState[s]] = n.next[s]

          } else { // if the swapping node is not the head, we must construct our frame conditions differently
            one j: IntNode | {
              j.next[s] = i
              j.next[LinkedList.nextState[s]] = i.next[s]

              //frame condition --> since there is a previous node, we also frame the head since this node cannot be the head
              LinkedList.head[s] = LinkedList.head[LinkedList.nextState[s]]
              all n: IntNode - (i + j + i.next[s]) | n.next[LinkedList.nextState[s]] = n.next[s]
            }
          } 
        }

      // if the list is already sorted, we still need these frame conditions
      } else {
        LinkedList.head[LinkedList.nextState[s]] = LinkedList.head[s]
        all i: IntNode | i.next[LinkedList.nextState[s]] = i.next[s]
      }
    }
  }
}


---------------------------------------------------------------

pred someList {
    some l: LinkedList | wellformed and newInsertion and swapping
}
run { // numbers are arbitrary, however need at least two states and two nodes
  someList
 } for exactly 5 IntNode, exactly 6 State, exactly 1 LinkedList for {nextState is linear}


 