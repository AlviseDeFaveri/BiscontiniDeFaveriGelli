open util/time
open util/integer

/** Signatures **/

-- Geographical position of the individuals
sig Position {
	latitude: one Int,
	longitude: one Int
}

-- Health status of individuals
abstract sig HealthStatus {}
-- Health status OK
one sig AboveThreshold extends  HealthStatus {}
-- Health status KO => AutomatedSOS calls Ambulance
one sig BelowThreshold extends HealthStatus {}


abstract sig User {}
sig Individual extends User {
	fiscalCode: one String,
	position: Position one -> Time,
	healthStatus: one HealthStatus
}
sig RunOrganizer extends User {}
sig RunParticipant extends Individual {}
sig RunSpectator extends Individual {}
sig ThirdParty extends User {}

abstract sig RequestStatus {}
one sig Accepted extends RequestStatus {}
one sig Denied extends RequestStatus {}

sig Request {
	individual: some Individual,
	requestStatus: one RequestStatus
} {
	#individual > 1 implies (requestStatus = Accepted <=> #individual >=  1000)
}

sig Path {}
sig Run {
	path: one Path,
	organizers: some RunOrganizer,
	participants: some RunParticipant,
	spectators: set RunSpectator
}

/** Facts **/

-- There cannot be two users with the same fiscal code
fact fiscalCodeIsUnique {
	no disjoint i1, i2: Individual | i1.fiscalCode = i2.fiscalCode
}

/** Dynamic Model **/

pred enrollParticipantToRun [r, r': Run, p: RunParticipant] {
	r'.participants = r.participants + p
}



