/** Signatures **/

-- Fiscal Code should be a string, here it's an int to be able to do operation on it (not permitted on string type in alloy)
sig User {
fiscalCode: one Int,
userData: one UserData,
sources: some DataSource
}
sig UserData extends RequestableData {
owner: one User,
parameters: set Parameter
}
sig DataSource {
owner: one User,
parameters: set Parameter
}
-- values of the Parameters are here commented because there isn't any check on them in the model
abstract sig Parameter {
source: one DataSource
}
sig Position extends Parameter {
--latitude: one Int,
--longitude: one Int
}
sig HearthRate extends Parameter {
--value: one Int
}
sig Pressure extends Parameter {
--value: one Int
}
sig ThirdParty {
vatCode: one Int,
}
sig DataRequest {
owner: one ThirdParty,
subType: one SubscriptionType,
status: one Status,
content: one RequestableData
}
abstract sig SubscriptionType {}
one sig OneShot extends SubscriptionType {}
one sig Subscription extends SubscriptionType {}

abstract sig Status {}
one sig Accepted extends Status {}
one sig Refused extends Status {}
one sig Pending extends Status {}

abstract sig HealthStatus {}
one sig HealthyStatus extends HealthStatus {}
one sig EmergencyStatus extends HealthStatus {}

-- RequestableData is the content of a thirdParty request, that can be for a single UserData or for GroupData, composed of many UserData
abstract sig RequestableData {
}
sig GroupData extends RequestableData {
usersData: some UserData
}
/* AutomatedSOS signatures*/

sig AutomatedSOSUser extends User {
healthStatus: one HealthStatus,
thresholds: some Threshold
}
sig Threshold {
owner: one AutomatedSOSUser,
paramType: one Parameter,		
minValue: one Int,
maxValue: one Int
} {minValue < maxValue}
one sig MonitoringService extends ThirdParty {
monitoredASOSUser: set AutomatedSOSUser
}
one sig AmubulanceAPI {
}
/* Track4Run signatures*/

sig Runner extends User {
scheduledRuns: some Run
}
sig Organizer extends User {
organizedRuns: some Run
}
sig Spectator extends User {
}
sig Run {
organizer: one Organizer,
partecipants: set Runner,
startTime: one Int,
endTime: one Int
}
one sig TrackingService extends ThirdParty {
monitoredRunners: set Runner
}
one sig MapsAPI {
--connected to the TrackingService
}
/** Data4Help Facts **/

fact noEqualFiscalCode {
no disj u1,u2: User |  (u1.fiscalCode = u2.fiscalCode)
}
fact noEqualVATcode {
no disj t1,t2: ThirdParty | (t1.vatCode = t2.vatCode)
}
-- Over 1000 data makes the request successfull
fact groupDataExistence {
all g: GroupData | #g.usersData > 1  -- This should be 1000 but it's unfeasible to verify our model in a scope that large
}
-- Consistency of signatures connections 
fact UserDataOwnership {
all u: User , ud: UserData | (ud.owner = u iff u.userData = ud )
}
fact UserSourcesOwnership {
all u: User , s: DataSource | ( (s in u.sources) implies s.owner = u ) and ( s.owner = u implies ( s in u.sources ) )
}
fact SourceParamOwnership {
all s: DataSource, p: Parameter | ( (p in s.parameters) implies p.source = s) and ( p.source = s implies (p in s.parameters))
}
-- All parameters tracked by a User's sources are present in the user's userData
fact userDataContainsAllSourcesParameters {
all ud: UserData, u: User, s: DataSource, p: Parameter | (ud.owner = u and (s in u.sources) and (p in s.parameters)) implies (p in ud.parameters)
}
-- Only parameters tracked by a User's sources are present in the user's userData
fact userDataContainsOnlyUserSourceParam {
all ud: UserData, u: User, s: DataSource, p: Parameter | ((ud.owner = u) and (not s in u.sources)) implies (( p in s.parameters) implies (not p in ud.parameters)) 
}
-- For each Parameter Type a declaration that every userData has at max one instance of it
fact userDataMaxOnePosition {
all ud: UserData | no disj p1,p2: Position | ((p1 in ud.parameters) and (p2 in ud.parameters))
}
fact userDataMaxOneHeartRate {
all ud: UserData | no disj hb1,hb2: HearthRate | ((hb1 in ud.parameters) and (hb2 in ud.parameters))
}
fact userDataMaxOnePressure {
all ud: UserData | no disj bp1,bp2: Pressure | ((bp1 in ud.parameters) and (bp2 in ud.parameters))
}
/** AutomatedSOS Facts **/

-- All AutomatedSOSUsers are monitored by the MonitoringService
fact ASOSUinMonitoredList {
all au: AutomatedSOSUser | au in MonitoringService.monitoredASOSUser
}
-- MonitoringService never makes request not for UserData of a ASOS user
fact noOtherReqMonitoring {
no dr: DataRequest | all rd: RequestableData | (dr.owner = MonitoringService) and (dr.content = rd) and ( rd in GroupData or rd.owner not in AutomatedSOSUser)
}
-- Consistency of signatures connection
fact autoSOSuserThresholdOwnership {
all u: AutomatedSOSUser | all t: Threshold | (t in u.thresholds) iff (t.owner = u)
}
-- All request of MonitoringService are Accepted and Subscribed
fact monitoringServiceRequestAreSubAccSingle {
all r: DataRequest | one m: MonitoringService | r.owner = m implies ( (r.status in Accepted) and (r.subType in Subscription) )
}
-- Each AutomatedSOSUser has a DataSource that has Position as a parameter (location is needed to provide AutomatedSOS services)
fact ASOSUserNeedsLocation {
all u: AutomatedSOSUser | one s: DataSource | one p: Position | ( s in u.sources ) and ( p in s.parameters )
}
-- Only Param of AutomatedSOSUser can have a threshold
fact noThresholdForNonASOSUser {
all t: Threshold | one au: AutomatedSOSUser | all s: DataSource | ( (s in au.sources) and (au.thresholds = t) ) iff ( t.paramType in s.parameters) 
}

-- Threshold aren't applied to the Position
fact noThresholdPosition {
all t: Threshold | no p: Position | t.paramType = p
}
-- No more than one Threshold for each type of Param
fact noMultipleThresholdSameParam {
no disj t1,t2: Threshold | no hr: HearthRate | no p: Pressure | ( (t1.paramType = p) and (t2.paramType = p) ) and ( (t1.paramType = hr) and (t2.paramType = hr) ) 
}

/** Track4Run facts **/ 

-- All Runners are tracked by the TrackingService
fact runnerInTrackerList {
all r: Runner | r in TrackingService.monitoredRunners
}
-- TrackingService never makes request not for UserData of a Runner
fact noOtherReqTracking {
no dr: DataRequest | all rd: RequestableData | (dr.owner = TrackingService) and (dr.content = rd) and ( rd in GroupData or rd.owner not in Runner)
}
-- All request of TrackingService are Accepted and Subscribed
fact trackingServiceRequestAreSubAccSingle {
all r: DataRequest | one t: TrackingService | r.owner = t implies ( (r.status in Accepted) and (r.subType in Subscription) )
}
-- Consistency of signatures connection
fact runnerEnrolledRunConnection {
all rer: Runner | all r: Run | ( r in rer.scheduledRuns) iff ( rer in r.partecipants)
}
fact organizerRunOwnership {
all o: Organizer | all r: Run | ( r in o.organizedRuns) iff ( o = r.organizer )
}
-- Each Runner has a DataSource that has Position as a parameter (location is needed to provide Track4Run services)
fact RunnerNeedsLocation {
all u: Runner | one s: DataSource | one p: Position | ( s in u.sources ) and ( p in s.parameters )
}
-- No runner can be enrolled to multiples runs that appens at the same time
fact noMultipleRunEnrollmentAtSameTime {
all r: Runner | no disj r1,r2: Run | -- all the possibility for overlapping runs
( ( r1.startTime < r2.startTime and r1.endTime > r2.endTime ) or ( r2.startTime < r1.startTime and r1.startTime < r2.endTime ) ) and 
( r1 in r.scheduledRuns ) and ( r2 in r.scheduledRuns )
}

pred show {
(one u:User | #u.sources >=2) and 
(some dr: DataRequest | dr.content = GroupData)
}
assert ASOSUserAlwaysHasPosition {
all au: AutomatedSOSUser | one p: Position | p in au.userData.parameters
}
assert RunnerAlwaysHasPosition {
all r: Runner | one p: Position | p in r.userData.parameters
}

run show for 8 but exactly 2 AutomatedSOSUser, exactly 1 Runner, exactly 1 Run, exactly 1 Organizer, exactly 3 ThirdParty, exactly 5 User, exactly 4 DataRequest

check ASOSUserAlwaysHasPosition
check RunnerAlwaysHasPosition