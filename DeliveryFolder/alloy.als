/** Signatures **/
open util/boolean

sig User {
parameters: some TrackedParameter,
sources: some DataSource
}
sig DataSource {
owner: one User,
parameters: some TrackedParameter
}

sig TrackedParameter {
source: one DataSource,
user: one User,
type: one ParameterType,
value: one Int,
threshold: lone Threshold
}

abstract sig ParameterType {}
one sig Position extends ParameterType {}
one sig HearthRate extends ParameterType {}
one sig Pressure extends ParameterType {}

sig ThirdParty {
requests: set Request
}
one sig AutomatedSOS extends ThirdParty {}

sig Request {
owner: one ThirdParty,
status: one Status,
filters: set Filter,
targetUser: lone User
} { ((filters != none) iff (targetUser = none)) and ((filters = none) 

iff (targetUser != none)) }

sig Filter {
ownerRequest: one Request,
paramType: one ParameterType,
min: one Int,
max: one Int
}

sig Group {
members : set User,
request: one Request
}

abstract sig Status {}
one sig Accepted extends Status {}
one sig Denied extends Status {}

sig Threshold {
min: one Int,
max: one Int,
parameter: one TrackedParameter
} 

abstract sig EmergencyStatus {}
one sig Normal extends EmergencyStatus {}
one sig Emergency extends EmergencyStatus {}

sig AutomatedSOSUser extends User {
status: one EmergencyStatus
}

sig Runner extends User {
partecipate: some Run
}
sig Organizer extends User {
organize: some Run
}
sig Spectator extends User {
watching: one Run
}
sig Run {
owner: one Organizer,
partecipants: set Runner,
maxPartecipants: one Int,
ongoing: one Bool
} {#partecipants <= maxPartecipants}

one sig Track4Run extends ThirdParty {}

/** Data4Help Facts **/

/* User Condition*/
-- Consistency of signatures connections 
fact UserHasParam {
all u: User , p: TrackedParameter | (p.user = u iff (p in u.parameters ))
}
fact UserSourcesOwnership {
all u: User , s: DataSource | ( (s in u.sources) implies s.owner = u ) and ( s.owner = u implies ( s in u.sources ) )
}
fact SourceParamConnection {
all s: DataSource, p: TrackedParameter | ( (p in s.parameters) implies p.source = s) and ( p.source = s implies (p in s.parameters))
}
fact UserSourceTrackedParamConnection {
all u: User | all s: DataSource | all p: TrackedParameter |
(( s in u.sources) and (p in s.parameters)) implies (p in u.parameters)
}
-- For each Parameter Type a declaration that every User has at max one tracked instance of it 
fact userMaxOneParamPerType {
all u: User | no disj tp1,tp2: TrackedParameter | ((tp1 in u.parameters) and (tp2 in u.parameters)) and ( tp1.type = tp2.type)
}
-- No filter of the same request can affect the same parameter type
fact filterMaxOneParamPerType {
no disj f1,f2: Filter | (f1.ownerRequest = f2.ownerRequest) and (f1.paramType = f2.paramType) 
}

/* ThirdParty & Requests */
fact ThirdPartyRequestOwnership {
all tp: ThirdParty | all r: Request | (r in tp.requests) iff ( tp = r.owner)
}
fact RequestFilterOwnership {
all r: Request | all f: Filter | (f in r.filters) iff ( r = f.ownerRequest)
}
-- Each Request for a targetUser is as default accepted (the acceptance is the one made by the system, prior to user real acceptance of a request)
fact targetUserRequestAreAccepted {
all r: Request | (r.targetUser != none) implies (r.status = Accepted)
}
-- for the sake of simplicity and because the scope is limited, the threshold for anonymization is set to 2
fact filteredRequestAcceptance {
all r: Request, g: Group | (r in g.request) implies ( ( r.status = Accepted) iff ( #g.members >=2) )
}
fact RequestAcceptance {
all r: Request, g: Group | (r.status in Accepted) iff ( not(r.targetUser = none) or ((r in g.request) and (#g.members >= 2)))
}

/* Groups */
-- A request refers to a group of user <=> it has filters and it doesn't refers to a single target user
fact GroupsBelongToFilteredRequests {
all g:Group, r:Request | (r = g.request) iff ((r.filters != none) and (r.targetUser = none))
}

-- If a request refers to a group of user and the filters are on a ParamType present in that group user's TrackedParameters, than the TrackedParam's value are within the filter range
fact GroupMembersAreFiltered {
all g:Group | all u:User | all r:Request | all f:Filter | all p:TrackedParameter |	(u in g.members) and (r = g.request) and (f in r.filters) and (p in u.parameters) implies ((f.paramType = p.type) implies (p.value >= f.min and p.value <= f.max))
}
-- A request without filter doesn't refer to a group of user, while a request with filter refers at max to one group of user
fact eachFilterReqHasGroup {
all r:Request | ((r.filters = none) implies ((r.targetUser != none) and (no g:Group | g.request = r)))
​			and ((r.filters != none) implies ((r.targetUser = none)  and (no disj g1,g2:Group | g1.request = g2.request)))
}
-- for each user in a group of a request, exactly one TrackedParam of that user has type equal to a filter of that group
fact GroupMembersHaveFilteredParams {
all g:Group, u:User, r:Request, f:Filter |
​			 ((u in g.members) and (r = g.request) and (f in r.filters)) implies (one p:TrackedParameter | (p in u.parameters) and (p.type = f.paramType))
}

/** AutomatedSOS **/

-- AutomatedSOS makes request only for AutomatedSOS Users
fact AutoSOSMonitorOnlyAutoSOSUser {
all r: Request | (r.owner = AutomatedSOS) implies (one au: AutomatedSOSUser |(r.targetUser = au))
}

-- Threshold ownerParam and TrackedParameter threshold must be consistent
fact thresholdTrackedParamConsistency {
all th: Threshold, p: TrackedParameter | (p.threshold = th) iff (th.parameter = p)
}
-- AutomatedSOS makes one request for each AutomatedSOS User
fact allAutoSOSUserAreMonitored {
all au: AutomatedSOSUser | one r: Request | (r.owner = AutomatedSOS) and (r.targetUser = au) 
}
-- All AutomatedSOSUser have HearthRate tracked
fact AutomatedSOSTrackedParamPresence {
all au: AutomatedSOSUser | one p: TrackedParameter | ( p in au.parameters) and (p.type = HearthRate)
}
-- All AutomatedSOSUser have a threshold set for their HearthRate
fact thresholdPresence {
all au: AutomatedSOSUser, p: TrackedParameter | ((p in au.parameters) and (p.type = HearthRate)) implies (one th: Threshold | th in p.threshold)
}
-- Only AutomatedSOSUser have a threshold set for any TrackedParameter, any other User has no threshold
fact thresholdAbsenceForNonAutoSOSUser {
all u: User | not(u in AutomatedSOSUser) implies (no p: TrackedParameter | (p in u.parameters) and (one th: Threshold | th in p.threshold))
}
/* TrackedParameters != HearthRate cannot have threshold 
​	(this is valid only for this model, if other parameters needs to be checked in order to control user's health status this and other facts need to change)*/
fact OnlyHearthRateIsMonitored {
all p: TrackedParameter | (p.type != HearthRate) implies (no th: Threshold | (th in p.threshold))
}
-- A AutomatedSOSUser is in an emergency status <=> his HearthRate broke the Threshold
fact userNeedsAmbulance {
all au: AutomatedSOSUser | (one p: TrackedParameter |(p in au.parameters) and (p.type = HearthRate) and (p.value > p.threshold.max or p.value < p.threshold.min)) iff (au.status = Emergency)
}


/** Track4Run **/ 
-- Consistency of Track4Run signatures
fact OrganizerRunConsistency {
all r: Run, o: Organizer | (r in o.organize) iff (o = r.owner)
}
fact RunnerRunConsistency {
all rn: Runner, r: Run | (rn in r.partecipants) iff (r in rn.partecipate)
}
-- All Runners iscribed to Track4Run must have a device able to track their position
fact runnerPositionPresence {
all rn: Runner | one p: TrackedParameter | (p in rn.parameters) and (p.type = Position)
}
-- Track4Run makes request only to Runners
fact track4RunMonitorsOnlyRunners {
all r: Request | (r.owner = Track4Run) implies (one rn: Runner |(r.targetUser = rn))
}
-- Track4Run makes one request for each Runner
fact allRunnersAreMonitored {
all rn: Runner | one r: Request | (r.owner = Track4Run) and (r.targetUser = rn) 
}
-- All Runner have Position tracked
fact runnerPositionPresence {
all rn: Runner | one p: TrackedParameter | ( p in rn.parameters) and (p.type = Position)
}

pred runIsFull[r: Run] {
#r.partecipants = r.maxPartecipants
}
pred enrollToRun[rn: Runner, r: Run] {
not runIsFull[r]
r.partecipants = r.partecipants + rn
}
pred watchRun[r: Run, s: Spectator] {
r.ongoing = True
some rn: Runner | (rn in r.partecipants) and (one p: TrackedParameter | (p in rn.parameters) and (p.type = Position))
s.watching = r
}

/* Int conversion to positive values + min/max consistency */
fact intToPositiveAndConsistency {
all tp: TrackedParameter, f: Filter, th: Threshold | (tp.value >= 0) 
​		and (f.min >= 0) and (f.max >=0) and (f.min < f.max)
​		and (th.min >=0) and (th.max >=0) and (th.min < th.max)
}
-- Check that every request that violates the anonymization restriction ( at least 2 user respect the filters ) is denied by the system
assert GroupDataAcceptance {
all r: Request, g: Group | (r.status in Denied) iff ((r.targetUser = none) and ((r in g.request) and ( #g.members < 2)))
}
-- Check that every AutomatedSOSUser that has his HearthBeat in the safe zone of its threshold can't be in an emergency status
assert AutoSOSUserHealthyAreNotInEmergency {
all au: AutomatedSOSUser | all p: TrackedParameter | ((p in au.parameters) and (p.type = HearthRate) and (p.value > p.threshold.min and p.value < p.threshold.max)) implies (au.status = Normal)
}

pred show {
(#AutomatedSOSUser = 2)
(one au: AutomatedSOSUser | au.status = Normal)
(one au: AutomatedSOSUser | au.status = Emergency)
(#Runner = 2)
(#Spectator =1)
(#Run = 1)
( #Group >=1) 
( #Request >=1)
(one g: Group | #g.members = 1)  //This is to show at least one Request that is declined
(lone u: User | #u.parameters = 3) //Only one user will have all 3 parameters, to keep the World Generated Readable
}

run show for 8 but exactly 6 User, exactly 5 Request, exactly 3 ThirdParty, exactly 2 Filter
run enrollToRun for 8
run watchRun for 8
check GroupDataAcceptance for 8
check AutoSOSUserHealthyAreNotInEmergency for 8
