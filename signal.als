
// Names of you and your partner:
// Jun Li Chen, Emmanuel Pinca

// the type of addresses
abstract sig Address {}

// some addresses are controlled by potential attackers
sig AttackerAddress extends Address {}

// one address belongs to the User who we model in this file
one sig UserAddress extends Address {}

// the four message types used in the protocol
abstract sig MessageType {}
one sig SDPOffer, SDPAnswer, SDPCandidates, Connect 
  extends MessageType {}

// a message has a type, plus a source (sender) and
// destination (receiver) addresses
sig Message {
  type  : MessageType,
  source: Address,
  dest  : Address,
}


// the seven recorded call states
// SignallingOffered, SignallingOngoing are used only by the caller
// SignallingStart, SignallingAnswered, and Answered are used by the 
// callee
// SignallingComplete is used by both caller and callee
abstract sig CallState {}
one sig SignallingStart, SignallingOffered, SignallingAnswered,
        SignallingOngoing,
        SignallingComplete, Answered, Connected 
  extends CallState {}


/* caller                                 callee
   ------                                 ------
                   ---- SDPOffer --->  
   SignallingOffered                          
                                          SignallingStart
                    <--- SDPAnswer ----
                                          SignallingAnswered
   SignallingOngoing
                  ---- SDPCandidates --->
   SignallingComplete
                                          SignallingComplete
                                                              ------ ringing >> 
                                                              <<--- user answers
                                          Answered
                  <---- Connect -------
                                          audio connected
   audio connected
                                          
*/
   
// the state of the system
one sig State {
  var ringing: lone Address, // whether the User is ringing and if so for whicih caller
  var calls: Address -> lone CallState, // the recorded call state for each call currently in progress
  var audio: lone Address,  // the participant that the User's audio is connected to
  var last_answered: lone Address, // the last caller the User answered a call from
  var last_called: lone Address,   // the last callee that the User called
  var network: lone Message        // the network, records the most recent message sent 
}


// precondition for the User to send a message m in state s
pred user_send_pre[m : Message] {
  m.source in UserAddress and
  (
   (m.type in SDPOffer and m.dest = State.last_called and no State.calls[m.dest]) or
   (m.type in SDPAnswer and State.calls[m.dest] = SignallingStart) or
   (m.type in SDPCandidates and State.calls[m.dest] = SignallingOngoing) or
   (m.type in Connect and State.calls[m.dest] = Answered and State.last_answered = m.dest)
  )
}

// precondition for the User to receive a message m in state s
// pred user_recv_pre[m : Message] {
//   m in State.network and
//   m.dest in UserAddress and
//   (
//    (m.type in SDPOffer and no State.calls[m.source]) or
//    (m.type in SDPAnswer and State.calls[m.source] = SignallingOffered) or
//    (m.type in SDPCandidates and State.calls[m.source] = SignallingAnswered) or
//    (m.type in Connect and State.calls[m.source] = SignallingComplete)
//   )
// }

// postcondition for the user sending a message m.
// s is the state the message is sent in and s' is the state
// after sending the message
//
// No need to specify here that last_called and last_ answered to not change
pred user_send_post[m : Message] {
  State.network' = m and
  // FILL IN HERE
  m.dest in AttackerAddress and
  State.ringing' = State.ringing and
  (
    (
      m.type in SDPOffer and
      State.calls' = State.calls ++ (m.dest -> SignallingOffered) and
      State.audio' = State.audio
    ) or (
      m.type in SDPAnswer and
      State.calls' = State.calls ++ (m.dest -> SignallingAnswered) and
      State.audio' = State.audio
    ) or (
      m.type in SDPCandidates and
      State.calls' = State.calls ++ (m.dest -> SignallingComplete) and
      State.audio' = State.audio
    ) or (
      m.type in Connect and
      State.calls' = State.calls and
      State.audio' = m.dest
    )
  )
}

// postcondition for the user receiving a message m
// s is the state before the message was received; s'
// is hte state after the message was received
//
// No need to specify here that last_called and last_answered to not change
pred user_recv_post[m : Message] {
  no State.network' and
  // FILL IN HERE
  m.source in AttackerAddress and
  (
    (
      m.type in SDPOffer and
      State.calls' = State.calls ++ (m.source -> SignallingStart) and
      State.ringing' = State.ringing and
      State.audio' = State.audio
    ) or (
      m.type in SDPAnswer and
      State.calls' = State.calls ++ (m.source -> SignallingOngoing) and
      State.ringing' = State.ringing and
      State.audio' = State.audio
    ) or (
      m.type in SDPCandidates and
      State.calls' = State.calls ++ (m.source -> SignallingComplete) and
      State.ringing' = m.source and
      State.audio' = State.audio
    ) or (
      m.type in Connect and
      State.calls' = State.calls and
      State.ringing' = State.ringing and
      State.audio' = m.source
    )
  )
}

// the action of the attacker sending a message
// s is the state before the message is sent, s' is the state after
pred attacker_msg {
  some m : Message | m.source in AttackerAddress and
  State.network' = m and
  State.calls' = State.calls and
  State.audio' = State.audio and
  State.ringing' = State.ringing and
  State.last_called' = State.last_called and
  State.last_answered' = State.last_answered
}

// the action of the user either sending or receiving a message
pred user_msg {
  State.last_answered' = State.last_answered and
  State.last_called' = State.last_called and
  some m : Message |
    (user_send_pre[m] and user_send_post[m]) or
    (user_recv_pre[m] and user_recv_post[m])
}

// the action of the user deciding to answer a ringing call
// doing so removes the "ringing" information from the state
// and changes the recorded call state to Answered but otherwise
// does not modify anything
pred user_answers {
  some caller : Address |
  State.calls[caller] in SignallingComplete and
  State.ringing = caller and 
  State.audio' = State.audio and
  no State.ringing' and
  State.calls' = State.calls ++ (caller -> Answered) and
  State.last_answered' = caller and
  State.last_called' = State.last_called and
  State.network' = State.network
}

// teh action of the user deciding to call another participant
// doing so simply updates the last_called state and also cancels
// any current "ringing" state
// pred user_calls {
//   some callee : Address | State.last_called' = callee and
//   State.network' = State.network and
//   State.calls' = State.calls and
//   State.last_answered' = State.last_answered and
//   State.audio' = State.audio and
//   no State.ringing'   // calling somebody else stops any current ringing call
// }

pred state_unchanged {
  State.network' = State.network
  State.calls' = State.calls
  State.last_answered' = State.last_answered
  State.last_called' = State.last_called
  State.ringing' = State.ringing
  State.audio' = State.audio
}

// a state transition is either the user sending or receiving a msg
// or answering a call, or choosing to call somebody, or the attacker
// sending a message on the network
pred state_transition {
  user_msg or user_answers or
  attacker_msg  or user_calls
  or state_unchanged
}

// defines the initial state
// purposefully allow starting in a state where the User already
// wants to call somebody
pred init {
    no State.audio and no State.ringing and
    no State.last_answered and
    no State.network and
    all dest : Address | no State.calls[dest]
}

fact {
  init
}

fact {
  always state_transition
}



// a  bad state is one in which the User's audio is connected
// to a participant but the User has not yet decided to call that
// participant or to answer a call from them
assert no_bad_states {
  // FILL IN HERE
  always {
    all a : Address |
      State.audio = a =>
      (
        // User as caller
        (State.last_called = a and State.calls[a] = SignallingComplete) or
        // User as callee
        (State.last_answered = a and State.calls[a] = Answered)
      )
  }
}

// describe the vulnerability that this check identified
// The markers will reverse the "fix" to your model that you
// implemented and then run this "check" to make sure the vulnerability
// can be seen as described here.
// FILL IN HERE
// EXPLANATION: 

// Choose a suitable bound for this check to show hwo the
// vulnerability does not arise in your fixed protocol
// Justify / explain your choice of your bound and
// specifically, what guarantees you think are provided by this check.
// See the assignment handout for more details here.
// FILL IN HERE
check no_bad_states for 7 // CHOOSE BOUND HERE
// JUSTIFICATION:
// bounds lower than 7 cannot reliably generate a counterexample of the fault 
// in the protocol.
// bounds higher than 7 is too computationally expensive.
// 7 serves as a good middle ground which is able to reliably generate a 
// counterexample while not taking forever to finish searching through the
// possible combinations of variables.

// Alloy "run" commands and predicate definitions to
// showing successful execution of your (fixed) protocol
// These should include
// (1) The user successfully initiates a call (i.e. is the caller), 
// resulting in their audio being connected to the callee
// (2) The user makes a call and receives a call in the same 
// execution trace, so that in one state their audio is connected 
// to one participant and in another state it is connected to some
// other participant
// FILL IN HERE
pred simulate_call {
  some m: Message, u: UserAddress, a: AttackerAddress | 
    init 
      => after
      (m.type = SDPOffer and 
      m.source = u and 
      m.dest = a
      and State.network = m)
        // this doesnt work not sure how to check subsequent messages
        => after
        (m.type = SDPAnswer and 
        m.source = a and 
        m.dest = u
        and State.network = m)
}

pred simulate_answer {
}

run simulate_call
run simulate_answer

// Describe how you fixed the model to remove the vulnerability
// FILL IN HERE
// FIX:
pred user_recv_pre[m : Message] {
 m in State.network and
 m.dest in UserAddress and
 (
  (m.type in SDPOffer and no State.calls[m.source]) or
  (m.type in SDPAnswer and State.calls[m.source] = SignallingOffered) or
  (m.type in SDPCandidates and State.calls[m.source] = SignallingAnswered) or
  (m.type in Connect and State.calls[m.source] = SignallingComplete and State.last_called = m.source)
 )
}

pred user_calls {
 some callee : Address | no State.last_called and
 State.last_called' = callee and
 State.network' = State.network and
 State.calls' = State.calls and
 State.last_answered' = State.last_answered and
 State.audio' = State.audio and
 no State.ringing'
}
// Your description should have enough detail to allow somebody
// to "undo" (or "reverse") your fix so we can then see the vulnerability
// in your protocol as you describe it in comments above
