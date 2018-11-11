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
userDataList: set RequestableData  -- lista di request accettate di ownate dal thirdParty
}

sig DataRequest {
owner: one ThirdParty,
subType: one SubscriptionType,
status: one Status,
content: one RequestableData,
dataType: one DataType
}

abstract sig DataType {}
one sig SingleUserDataType extends DataType {}
one sig GroupDataType extends DataType {}

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

-- RequestableData is the content of a thirdParty request, that can be for a UserData or for aggregated data
abstract sig RequestableData {
subscribersList: set ThirdParty
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
-- Si potrebbe mettere una monitoredUsersList: AutoSOSUser && monitoredUsersData: set UserData && monitoredHealthStatuses: set HealthStatus
-- for all request of a Monitoring system ThirdParty status=Accepted
}

one sig AmubulanceAPI {
-- it's called and the location is passed as a parameter
}

/* Track4Run signatures*/

								-- sia Runner che Organizer sono differenziati da User <=> almeno una gara nei loro attrib., quindi some
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






/** Facts **/

fact noEqualFiscalCode {
no disj u1,u2: User |  (u1.fiscalCode = u2.fiscalCode)
}
fact noEqualVATcode {
no disj t1,t2: ThirdParty | (t1.vatCode = t2.vatCode)
}
-- Over 1000 data makes the request successfull
fact groupDataExistence {
no g: GroupData | #g.usersData > 999
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

-- all request in the openSubscription list of a third party are owned by them and each of these req is accepted and subscribed
--fact thirdPartyDataRequestOwnership {
--all t: ThirdParty | all r: DataRequest | ( r in t.openSubscription iff (r.owner = t and r.subType=Subscription and r.status= Accepted))
--}

-- DataRequest Type must be consistent with the type of content of the DataRequest
fact dataTypeRequestConsistency {
all dr: DataRequest | (dr.dataType = SingleUserDataType iff dr.content = UserData) and ( dr.dataType = GroupDataType iff dr.content = GroupData ) 
}

-- RequestableData has a Third party in the subscribersList implies that a dataRequest by that thirdParty and with that requestableData as content must exists
fact dataSetExistance {
--all rd: RequestableData | 
}
-- RequestableData has in his subscribersList all the Third parties that have a request for that requestable data Accepted and Subscribed
fact ListenerOpenSubCoerence {
all rd: RequestableData | no r: DataRequest | all tp: ThirdParty | tp in rd.subscribersList iff !( r.content = rd and r.owner = tp)
}
-- The same Third Party cannot make request for RequestableData that are in his userDataList
fact noMoreThanOneSameRequest {
all tp: ThirdParty | all dr: DataRequest 

/** AutomatedSOS facts**/

-- Consistency of signatures connection
fact autoSOSuserThresholdOwnership {
all u: AutomatedSOSUser | all t: Threshold | (t in u.thresholds) iff (t.owner = u)
}

-- All request of MonitoringService are Accepted and Subscribed
fact monitoringServiceRequest {
all r: DataRequest | one m: MonitoringService | r.owner = m implies ( r.status = Accepted and r.subType = Subscription and r.dataType = SingleUserDataType )
}

-- Each AutomatedSOSUser has a DataSource that has Position as a parameter (location is needed to provide AutomatedSOS services)
fact ASOSneedsLocation {
all u: AutomatedSOSUser | one s: DataSource | one p: Position | ( s in u.sources ) and ( p in s.parameters )
}

-- the UserDatas in the userDataList of the MonitoringService are all and only the UserData owned by AutomatedSOSusers
fact allAndOnlyASOSuserAreMonitored {
one m: MonitoringService | all ud: UserData | all dr: DataRequest | ( ( ud in m.userDataList ) iff ( ud.owner = AutomatedSOSUser ) ) and
( dr.owner = m iff dr.content.owner = AutomatedSOSUser )
}
-- This should be equal as stating that every UserData ownerd by a AutomatedSOSUser has in his subscribersList the MonitoringService
assert monitoringServiceInASOSUserDataSubscribers {
all ud: UserData | one m: MonitoringService | ud.owner = AutomatedSOSUser implies ( m in ud.subscribersList)
}

-- No more than one Threshold for each type of Param
fact noMultipleThresholdSameParam {
no disj t1,t2: Threshold | t1.owner = t2.owner and t1.paramType = t2.paramType
}
-- HealthStatus emergency <=> one of the threshold of the AutomatesSOSUser is broken
fact healthNOK {
--all u: AutomatedSOSUser | all hr: HearthRate | 
}




/** Track4Run facts **/ 

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

-- The tracking service keeps track of all the Runners that are enrolled to a (ongoing) run


/** Dinamic Model **/

pred makeArequest [r: DataRequest, tp: ThirdParty, t: SubscriptionType, s: Status, d: RequestableData] {
r.owner = tp
r.subType = t
r.status = s
r.content = d
}
pred show {
(some u:User | #u.sources >=2) --and
--(some ds: RequestableData | #ds.subscribersList > 0) --and
--(some suds: SingleUserDataSet | suds.userData.parameters ) and
--(some agds: AnonymousGroupDataSet | agds.parameters 
--(some r1,r2:Request | (r1.status = Accepted) and (r2.status = Refused) ) --and
--(some disj r1,r2:Request | (r1.subType = Subscription ) and (r2.subType = OneShot ) ) and
--(some disj r1,r2: Request | (r1.content = SingleUserDataSet) and (r2.content = AnonymousGroupData) )
}

--assert eachParamComesFromOneSource {
--all ud: Userdata, p: Parameter |
--}
--assert PressureComesFromOneSource
-- potrei fare un assert che verifica che tutti gli userdata di un user = AutomatedUserSOS hanno come listener nella lista il monitoring system







run show for 4 but exactly 1 AutomatedSOSUser, exactly 1 Runner, exactly 1 Run, exactly 1 Organizer, 10 DataRequest
--run makeArequest
check monitoringServiceInASOSUserDataSubscribers
