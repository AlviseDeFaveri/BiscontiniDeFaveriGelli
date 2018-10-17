open util/time
open util/integer

sig Position {
	latitude: one Int,
	longitude: one Int
}

abstract sig HealthStatus {}
one sig AboveThreshold extends  HealthStatus {}
one sig BelowThreshold extends HealthStatus {}

abstract sig User {}
sig Individual extends User {
	fiscalCode: one String,
	position: Position one -> Time,
	healthStatus: one HealthStatus
}
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

