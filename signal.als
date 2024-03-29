
// Names and ids of you and your partner:
// Jun Li Chen 1043258, Emmanuel Pinca 1080088

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
pred user_recv_pre[m : Message] {
  m in State.network and
  m.dest in UserAddress and
  (
   (m.type in SDPOffer and no State.calls[m.source]) or
   (m.type in SDPAnswer and State.calls[m.source] = SignallingOffered) or
   (m.type in SDPCandidates and State.calls[m.source] = SignallingAnswered) or
   (m.type in Connect and State.calls[m.source] = SignallingComplete)
  )
}

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
pred user_calls {
  some callee : Address | State.last_called' = callee and
  State.network' = State.network and
  State.calls' = State.calls and
  State.last_answered' = State.last_answered and
  State.audio' = State.audio and
  no State.ringing'   // calling somebody else stops any current ringing call
}

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
// VULNERABILITY:
// When an attacker calls the user, they can force the user to connect to their
// audio without the user answering. This vulnerability arises when the user
// as the callee reaches the SignallingComplete state and the attacker sends
// a Connect message afterwards. Since there is no distinction between the
// SignallingComplete state as a caller or callee, the user receives the
// Connect message as if it were a caller.

// Choose a suitable bound for this check to show hwo the
// vulnerability does not arise in your fixed protocol
// Justify / explain your choice of your bound and
// specifically, what guarantees you think are provided by this check.
// See the assignment handout for more details here.
// FILL IN HERE
check no_bad_states for 4 but 1 AttackerAddress, 8..8 steps expect 0 // CHOOSE BOUND HERE
// JUSTIFICATION:
// Having less than four top-level signatures cannot generate a counterexample
// of the assertion. This value only affects the number of messages and
// attackers simulated within the model, with the latter specified to only have
// a single instance. Only a single attacker is necessary to accomplish the
// attack as no attackers can modify the user's call state with other addresses
// and four messages will be created as it is the minimum needed to
// successfully connect audio (SDPOffer, SDPAnswer, SDPCandidates, Connect).
// Eight steps are necessary to check no_bad_states with a single connection. 
// As call states cannot be skipped, this is the exact number of steps required
// to connect audio without repeating messages that cannot be sent/read or
// executing the state_unchanged predicate.

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

// User initiating call predicate
pred simulate_call {
  some a: AttackerAddress |
    State.last_called = a and eventually State.audio = a
}

// User making and receiving call predicate
pred simulate_switch {
  some a1, a2: AttackerAddress, m1, m2, m3, m4, m5, m6, m7, m8: Message |
    a1 != a2 and

    m1.type = SDPOffer and
    m1.source in UserAddress and
    m1.dest = a1 and
    m2.type = SDPAnswer and
    m2.source = a1 and
    m2.dest in UserAddress and
    m3.type = SDPCandidates and
    m3.source in UserAddress and
    m3.dest = a1 and
    m4.type = Connect and
    m4.source = a1 and
    m4.dest in UserAddress and

    m5.type = SDPOffer and
    m5.source = a2 and
    m5.dest in UserAddress and
    m6.type = SDPAnswer and
    m6.source in UserAddress and
    m6.dest = a2 and
    m7.type = SDPCandidates and
    m7.source = a2 and
    m7.dest in UserAddress and
    m8.type = Connect and
    m8.source in UserAddress and
    m8.dest = a2 and

    eventually (
      State.last_called = a1 and State.last_answered != a1 and State.audio = a1
    ) 
    and eventually (
      State.last_answered = a2 and State.last_called != a2 and State.audio = a2
    )
}

// User initiates call, resulting with audio connected to callee (Task 2, 3.1)
run simulate_call for 4

// User makes and recieves two separate calls, switching audio (Task 2, 3.2)
// Assumes audio does not have to be connected immediately after answering call.
run simulate_switch for 8 but 14..14 steps

// Describe how you fixed the model to remove the vulnerability
// FILL IN HERE

// FIX:
// pred user_recv_pre[m : Message] {
//  m in State.network and
//  m.dest in UserAddress and
//  (
//   (m.type in SDPOffer and no State.calls[m.source]) or
//   (m.type in SDPAnswer and State.calls[m.source] = SignallingOffered) or
//   (m.type in SDPCandidates and State.calls[m.source] = SignallingAnswered) or
//   (m.type in Connect and State.calls[m.source] = SignallingComplete and State.last_called = m.source) // Change #1
//  )
// }

// pred user_calls {
//  some callee : Address | State.last_called' = callee and
//  State.network' = State.network and
//  State.calls' = State.calls and
//  State.last_answered' = State.last_answered and
//  State.audio' = none and // Change #2
//  no State.ringing'
// }

// Your description should have enough detail to allow somebody
// to "undo" (or "reverse") your fix so we can then see the vulnerability
// in your protocol as you describe it in comments above

// DESCRIPTION: 
// To undo the fix, comment out the above fixed predicates:
// user_recv_pre, user_calls
// uncomment the original predicates with the same name further above, and run
// the no_bad_states check.
// A counterexample will be found in the original predicates, whereas none
// will be found in the fixed predicates.
//
// The fix ensures Connect messages are only received when the user has
// recently decided to call an address (State.last_called = m.source) and
// clears the audio when another call is made (State.audio' = none). This
// prevents audio from connecting to anyone not called and stops any connected
// audio when another call is being made by the user. However this "minimal"
// fix assumes the audio does not have to be connected immediately after
// answering call and can connect audio to another call before finally
// connecting audio to the prior call.
