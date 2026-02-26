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

fun next_pair[i1, i2: IntNode, s: State]: set (IntNode -> IntNode) {
  {i1,i2: IntNode| i1.next[s] = i2}
  // {i1.next[s] = i2}
}

fun state_pair[s1,s2:State, l: LinkedList]: set (State -> State) {
  {s1,s2: State | l.nextState[s1] = s2}
}

fun edges[s: State]: set (IntNode -> IntNode) {
  {i, j: IntNode | i.next[s] = j}
}

pred distinctValues { // for visual clarity and to make the problem more interesting, we are forcing all nodes to be unique
  all disj a, b: IntNode | a.value != b.value
}


--------------------------------------------------------------------------------------
pred wellformed {
  all s: State| {LinkedList.nextState[s] != s}
  
  all disj s, s2: State {
    // acyclic
  
    all l: LinkedList, i1,i2: IntNode | {
      distinctValues
      
      s != l.firstState implies {reachable[s,l.firstState,state_pair[s,s2,l]]}
      l.nextState[l.firstState] != none // just need to force a second state to exist

      l.nextState[s] != l.firstState and l.nextState[s2] != l.firstState
      l.nextState[s] != l.nextState[s2] and l.nextState[s] != s

      sorted[l.firstState]

      not reachable[i1, i1, next_pair[i1, i2, s]]
      // head is not reachable through any node
      // i1 != l.head implies not reachable[l.head, i1, next_pair[i1, i2, l.firstState]]
      i1 != l.head[s] implies not reachable[l.head[s], i1, next_pair[i1, i2, s]]
      i2 = i1.next[s] implies {no i3: IntNode | {i3 != i1 and i2 = i3.next[s]}}


      // all nodes are reachable from head
      // i1 != l.head implies reachable[i1,l.head,next_pair[i1,i2, l.firstState]]

      i1 != l.head[s] and s != l.firstState implies reachable[i1,l.head[s],next_pair[i1,i2, s]]

      s = l.firstState implies {one i : IntNode | not reachable[i,l.head[s],edges[s]] and i!= l.head[s]}
    }
  }
}



pred sorted[s:State] {
  all i1,i2: IntNode|
      i1.next[s] = i2 implies i1.value < i2.value
}

pred newInsertion {
  let s = LinkedList.firstState | {
    let nx = LinkedList.nextState[s] {
      some nx
      some newNode: IntNode {
        not reachable[newNode, LinkedList.head[s], edges[s]]
        newNode != LinkedList.head[s]
        one tail: IntNode | {
          reachable[tail, LinkedList.head[s], edges[s]]
          no tail.next[s]

          tail.next[nx] = newNode
          no newNode.next[nx]


          //this line is just for testing purposes !!!!!!! please remember this lol :)
          newNode.value < LinkedList.head[LinkedList.firstState].value

          all n: IntNode - tail - newNode | n.next[nx] = n.next[s]
        }
      }
    }
  }
}



// pred swappingGood {
//   all s: State - LinkedList.firstState | {
//     some LinkedList.nextState[s] implies {
//       let ns = LinkedList.nextState[s] | {

//         not sorted[s] implies {

//           // There is exactly one adjacent out-of-order pair.
//           // Since the list is fully sorted except for one inserted element,
//           // this should always be satisfied with exactly one witness.
//           one j: IntNode | {
//             some j.next[s]                   // j must have a successor (guards tail node)
//             j.value > j.next[s].value        // j and its successor are out of order

//             let small = j.next[s] | {

//               // ── Core swap: always applies regardless of position ──
//               j.next[ns] = small.next[s]     // j skips over small to what small pointed to
//               small.next[ns] = j             // small now points back to j

//               // ── Head case: j IS the head ──
//               j = LinkedList.head[s] implies {
//                 LinkedList.head[ns] = small
//                 // Frame: only j and small changed their next pointers
//                 all n: IntNode - (j + small) | n.next[ns] = n.next[s]
//               }

//               // ── Non-head case: j has a predecessor ──
//               j != LinkedList.head[s] implies {
//                 LinkedList.head[ns] = LinkedList.head[s]   // head is unaffected
//                 // prev is the unique node pointing to j
//                 some prev: IntNode | {
//                   prev.next[s] = j
//                   prev.next[ns] = small
//                   // Frame: j, small, AND prev are the only nodes whose next changed
//                   all n: IntNode - (j + small + prev) | n.next[ns] = n.next[s]
//                 }
//               }

//             }
//           }

//         } else {
//           // Already sorted: hard freeze the entire state
//           LinkedList.head[ns] = LinkedList.head[s]
//           all n: IntNode | n.next[ns] = n.next[s]
//         }

//       }
//     }
      
//   }
// }







pred swapping {
  // There may exist some integer which is out of order
  // That integer swaps left in the next state if the node to the left has a value greater than that node
  // Frame condition: The next field of all nodes unaffected by the swap are the same

  // state cannot be FirstState because first state has not inserted the out of order element and thus is sorted

  all s: State - (LinkedList.firstState) | {  
    some LinkedList.nextState[s] implies {
      // i.next[s].value < i.value
      not sorted[s] implies {
        one i: IntNode | {
          some i.next[s]
          i.next[s].value < i.value
          i.next[LinkedList.nextState[s]] = i.next[s].next[s]
          i.next[s].next[LinkedList.nextState[s]] = i

          i = LinkedList.head[s] implies {
            //need some sort of predicate to handle the case where the head has to swap with another node
            i.next[s] = LinkedList.head[LinkedList.nextState[s]]
            
            // a -> c -> b
            // a -> b -> c
            //frame condition
            all n: IntNode - (i + i.next[s]) | n.next[LinkedList.nextState[s]] = n.next[s]
            // sorted[LinkedList.nextState[s]]

          } else { // this is okay for now ?
            one j: IntNode | {
              j.next[s] = i
              j.next[LinkedList.nextState[s]] = i.next[s]

              //frame condition --> since there is a previous node, we also frame the head since this node cannot be the head
              LinkedList.head[s] = LinkedList.head[LinkedList.nextState[s]]
              all n: IntNode - (i + j + i.next[s]) | n.next[LinkedList.nextState[s]] = n.next[s]
              // all n: IntNode - (i+j) | n.next[s].value > n.value
            }
          } 
        }


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
    // some l: LinkedList | wellformed and newInsertionV2 //and swappingV3
    // wellformed
    // newInsertionV2
    // swappingForced
}
run {
  someList
 } for exactly 5 IntNode, exactly 6 State, exactly 1 LinkedList for {nextState is linear}


 