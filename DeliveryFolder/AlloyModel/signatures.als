open util/time
open util/integer
open util/boolean

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
abstract sig Individual extends User {
	fiscalCode: one String
}
sig ThirdParty extends User {
	vatNumber: one String
}
sig Data4HelpUser extends User {
	position: Position one -> Time,
	healthStatus: one HealthStatus
}
sig RunOrganizer extends Individual {}
sig RunSpectator extends Individual {}
sig AutomatedSOSUser extends Data4HelpUser {}
sig Track4RunRunner extends Data4HelpUser {}


abstract sig RequestStatus {}
one sig Accepted extends RequestStatus {}
one sig Denied extends RequestStatus {}

sig Request {
	individual: some Individual,
	requestStatus: one RequestStatus
} {
	#individual > 1 implies (requestStatus = Accepted <=> #individual >=  1000)
}

abstract sig AmbulanceStatus {}
one sig Free extends AmbulanceStatus {}
one sig Busy extends AmbulanceStatus {}

sig Ambulance {
	status: one AmbulanceStatus
}

sig Path {}
abstract sig RunStatus {}
one sig NotStarted extends RunStatus {}
one sig Started extends RunStatus {}
one sig Finished extends RunStatus {}

sig Run {
	path: one Path,
	status: one RunStatus,
	organizers: some RunOrganizer,
	--participants: some RunParticipant,
	spectators: set RunSpectator
}

/** Facts **/

-- There cannot be two users with the same fiscal code
fact fiscalCodeIsUnique {
	no disj i1, i2: Individual | i1.fiscalCode = i2.fiscalCode
}

-- There cannot be two third parties with the same VAT number
fact vatNumberIsUnique {
	no disj t1, t2: ThirdParty | t1.vatNumber = t2.vatNumber
}

/** Dynamic Model **/

--pred enrollParticipantToRun [r, r': Run, p: RunParticipant] {
--	r'.participants = r.participants + p
--}

--pred callAmbulance [a: Ambulance

pred show {}
run show for 6


