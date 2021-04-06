------------------------------- MODULE Notes -------------------------------

Objective:

Explore and demonstrate how TLA+ specifications can directly be executed like a regular program. 
The runtime on which a TLA+ speicifcation executes, is Robbert van Renesse's PlusPy--a 
framework to map TLA+ processes and message channels defined in new standard modules to native
Python primitives (PlusPy is also a parser for a fragment of TLA+.  The parser has no support for
recursive operators, for TLAPS, ... yet).
We know that the performance of the execution will never be up to par with native implementations
in programming languages such as Python.  Instead, we target applications that can tolerate
the performance hit that results from executing a high-level spec in trade for high correctness
assurances.

* Take high-level, existing spec that has been model-checked and (ideally) proven correct
* Compose larger system out of it (and other specs)
* Execute on PlusPy

Microsoft Avere - Python cluster configuration

Idea:


Lets consider EWD998 (and its refinements sans ...ChanIDTermination) the *termination detection*
component.  A second component specifies how to actually shutdown nodes once termination has been
detected by the initiator node of EWD998.  Lastly, there will be a spec that models the computation
whose completion is detected by termination detection (EWD998). 


For verification with TLC, we can convert the open into a closed system by non-determinictically
generating inputs for the computation.  

TODOs/Issues/Open Questions:

  EWD998* component (TC):
  
   + Model node identities with addresses instead of natural numbers
   
   * Send/Receive termination messages (align with Messages.tla)
     Send operator has the problem that we end up changing the variable `inbox`
     twice in an action (for two nodes n, m we add element to `inbox[n]` /\ consume
     a message from `inbox[m]`). PlusPy delays message delivery because of the 
     msg interface variable s.t. the msg is added to inbox[n] in a successor state.
   
   * Merge all types of messages into a single type to hack around PlusPy limitation.
   * Fix PlusPy to handle multiple messages to get rid of message hack.
   
   * Use PlusPy Deliver approach
   
   + Proc(n) because we need a way to pass in the node's id (PlusPy)

  Shutdown component (SC):
    
    * Compose/combine/conjoin/interface SC and TC.
    
      * A spec (EWD998ChanIDTermination) that modelled SC and TC as a single component was 
        already model-checked with TLC.  It revealed an issue with EWD998's definition of
        the set of message types `Messages` that - in the combined spec - also has to
        include SC's termination message type. 
      * Specify assumptions of SC and TC.  Show that SC satisfies the assumptions of TC
        and vice-versa. 
      
      
    * Implement support for graceful shutdown in PlusPy (it is not possible to gracefully
      shutdown a PlusPy instance)
    
  Computation component (CC):
  
    * What should be the computation that's carried out?
      1) Conway's Game of Life
         + Termination has to be detected/not part of GOL
         - Round-based/Epochs that don't exist if each nodes represents a cell
      2) Echo (Stephan has an Echo spec already)
         ? Does it even require termination detection  
      3) Minimum spanning tree (Leslie's suggestion)
      
      
=============================================================================


----- MODULE EWD998ChanIDTermination ----

* The idea to make the current PlusPy process an argument of the next-state relation breaks
  with the standard TLA+ idiom (canonical way of writing specs): Next(n) vs. Next
  Not a big deal, but makes it a little bit more cumbersome to write fairness constraints and
  causes TLC to decompose the next-state relation into different sub-actions (which makes 
  coverage reporting to look strange). E.g. Termination below from EWD998ChanIDTermination
  is reported twice.
  
  Termination(n) ==
  \/ /\ n = Initiator
     /\ SendTermination
  \/ /\ n # Initiator
     /\ RecvTermination(n)
   

* Copy&Paste specs become a nuisance (programmers will hate it) with increasing levels of refinement

* Long chains of refinment mappings become a performance bottleneck
  * When to add intermediate "circuit breaks" as performance optimizations?
  * E.g. EWD998ChanID!EWD998Chan!EWD998!StateContraints becomes too expensive to 
    evaluate with multiple levels of refinement

* Substitute ordinary definitions such as Messages with CONSTANTS falls short when D of set of pre-
  defined values (e.g. cannot easily add TokenMsg and BasicMsg to CONSTANT Messages in TLC model)

* Composition of specs 
  * (Easy for specs with disjoint sets of variables, but what about two actions
    of spec A & B that both - at once - change var x where x appears in A and B)?
    => Abadi & Lamport - Conjoining Specifications

==========================================

---- Conjoining Specifications -----

Terminology in Conjoining Specs:
--------------------------------

Composition is reduced to conjunction:

Composition:
* Build a system bottom-up from smaller parts that have been proven correct individually.

Decomposition:
* Divide (and conquer) a larger system into smaller pars (components) to simplify reasoning
  about individual parts.

Composition and decomposition treat the environment differently and thus require different
proof rules.
  
Environment (E):
* Captures/Makes explicit the necessary assumptions under which a component (spec) exhibits
  its intended behavior (can work correctly).
  * A sufficiently hostile environment such as improper volate levels to a circuit will break 
    any component (the circuit).

Component:
* A spec describing a part of a system.

Guarantee (M):
* 

System (S):
* "complete system" is self-contained (does not interact with an observer)
* Consists of multiple components

Assume/Garantuee:
* Component satisfies a guarantee M only as long as its environment satisfies an assmption E.
* Denoted E -+-> M
* 
* E -+-> M => S


Complete Systems:
* A CS is one that is self-contained (may be observed but does not interact with the observer).
* Inputs of a CS are modelled as being generated non-deterministically.
* GCD is an example of a complete system.

Open Systems:
* An OS interacts with an environment it doesn't control.

Page 514, 3.1.2

Non-interleaving spec:
Interleaving spec:
* Simultaneous changes to variables x and y are disallowed.
* An interleaving spec is one where two components/processes are disallowed to change output

==========================================
