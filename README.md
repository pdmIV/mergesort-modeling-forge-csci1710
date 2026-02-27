# insertionsort-modeling-forge-csci1710
Midterm project for CSCI 1710 

Project Objective: What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.

We chose to model inserting a new node into a sorted, singly-linked list.  At a high level, our model generates a sequence of nodes which are only connected to their successor and cannot access their predecessor.  We start with nodes that are already sorted in increasing order, and then we add a node with some arbitrary value to our linked list.  The node propagates backward through the linked list until it is in its sorted position.

Model Design and Visualization: Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?

Our model is based on three sigs: State, IntNode, and LinkedList.  State is simply used to model the different timesteps of our model. In order to display the actual swapping of elements, we need State to arrange the IntNodes differently depending on the state.  The IntNode sig is our node class.  It has a value field which is just an Int, and a pfunc next which maps State to IntNode.  This pfunc is essential for modeling the swap as it allows us to change the successor node of any given node based on the current state.  LinkedList is the logic managing sig that connects everything together.  LinkedList has a pfunc head which maps State to IntNode that allows us to reference the top most node at any given timestep.  It also has a firstState field which contains the first State and allows us to proceed through timesteps linearly. Lastly, LinkedList has a pfunc nextState which maps State to State and simply maps each State to its successor State.

There are three primary predicates which control our model: wellformed, newInsertion, and swapping.  Wellformed is used to ensure that lists are initialized correctly.  We use wellformed mainly to sort the initial nodes and ensure there are no cycles, but there are various other edge cases captured here.  newInsertion handles the logic for adding a new node to the end of our linked list.  Finally, swapping has the basic linked list swapping logic as well as all of the necessary frame conditions.

We primarily used the run statement at the end of the file with the predicate someList.  We chose to force every element of our list to be unique, so it is important that the number of nodes in the run statement is less than the total number of Ints.  Additionally, we decided to make a constraint requiring every instance to contain at least two states, so the run statement needs at least 2.  We also specified that nextState in LinkedList is linear when running.  This avoids strange display issues where the firstState is not actually displayed chronologically.

Instances of our model utilitze the layout.cnd file we wrote for the default visualizer.  Instances project on the State sig, so in the layout tab there should be multiple tabs to look through the sorting process for our list.  The first two states will always show the original sorted list with the detached node, and then the new node attached to the end of the list in the second State.  All states that follow will show the sorting process (as long as there are sufficient states to fully sort the list), and then the list will remain sorted after the new node has been placed properly into the list.



Signatures and Predicates: At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.

Our model is based on three sigs: State, IntNode, and LinkedList.  State is simply used to model the different timesteps of our model. In order to display the actual swapping of elements, we need State to arrange the IntNodes differently depending on the state.  The IntNode sig is our node class.  It has a value field which is just an Int, and a pfunc next which maps State to IntNode.  This pfunc is essential for modeling the swap as it allows us to change the successor node of any given node based on the current state.  LinkedList is the logic managing sig that connects everything together.  LinkedList has a pfunc head which maps State to IntNode that allows us to reference the top most node at any given timestep.  It also has a firstState field which contains the first State and allows us to proceed through timesteps from a set starting point. Lastly, LinkedList has a pfunc nextState which maps State to State and simply maps each State to its successor State.

There are three primary predicates which control our model: wellformed, newInsertion, and swapping.  Wellformed is used to ensure that lists are initialized correctly.  We use wellformed mainly to sort the initial nodes and ensure there are no cycles, but there are various other edge cases captured here.  newInsertion handles the logic for adding a new node to the end of our linked list.  Finally, swapping has the basic linked list swapping logic as well as all of the necessary frame conditions.  There are various smaller predicates as well.  sorted checks that every next node has a strictly greater value than the one before (at a given timestep).  distinctValues forces every node to contain a unique value (we chose to do this to make the sorting problem more interesting than the trivial case).  We also use two helper functions, state_pair and edges, which are used in order to make use of reachable with LinkedList.nextState and IntNode.next respectively.




Testing: What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.

For the most part we just wrote positive and negative assertions for each predicate. We included extra tests for interesting properties, such as when a new node has a smaller value than the existing head and thus becomes the new head.  For swapping, instead of writing lengthy examples, we determined what properties were necessary for swapping to be valid.  We deduced that for swapping it is enough to show that we start from a valid state, move to an unsorted state, end in a sorted state, and our frame conditions hold.  This makes sense inductively because if we start from a valid state and only make valid moves, then it must be the case that our swap is valid.


Documentation: Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project.
