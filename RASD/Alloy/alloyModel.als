/** Signatures **/

sig User {
userData: one UserData,
sources: some Source
}
sig UserData {
owner: one User,
parameters: set Parameter
}
sig Source {
owner: one User,
parameters: some Parameter
}

abstract sig Parameter {
source: one Source
}
sig Position extends Parameter {
--latitude: one Int,
--longitude: one Int
}
sig HearthBeat extends Parameter {
--beatPerMinute: one Int
}
sig BloodPressure extends Parameter {
--pressure: one Int
}

sig ThirdParty {
openSubscription: set Request
}

sig Request {
owner: one ThirdParty,
subType: one SubscriptionType,
status: one Status,
content: one DataSet
}
abstract sig SubscriptionType {}
one sig NO_SUB extends SubscriptionType {}
one sig SUB extends SubscriptionType {}

abstract sig Status {}
one sig Accepted extends Status {}
one sig Refused extends Status {}

-- DataSet is the content of a thirdParty request, that can be for a UserData or for aggregated data
abstract sig DataSet {
listeners: set ThirdParty
}
sig SingleUserDataSet extends DataSet{
userData: one UserData
}
sig AnonymousGroupData extends DataSet{
parameters: set Parameter
}
/** Facts **/

fact UserDataOwnership {
all u: User , ud: UserData | (ud.owner = u iff u.userData = ud )
}
fact UserSourcesOwnership {
all u: User , s: Source | ( (s in u.sources) implies s.owner = u ) and ( s.owner = u implies ( s in u.sources ) )
}
fact SourceParamOwnership {
all s: Source, p: Parameter | ( (p in s.parameters) implies p.source = s) and ( p.source = s implies (p in s.parameters))
}
fact userDataContainsAllSourcesParameters {
all ud: UserData, u: User, s: Source, p: Parameter | (ud.owner = u and (s in u.sources) and (p in s.parameters)) implies (p in ud.parameters)
}
fact userDataContainsOnlyUserSourceParam {
all ud: UserData, u: User, s: Source, p: Parameter | ((ud.owner = u) and (not s in u.sources)) implies (( p in s.parameters) implies (not p in ud.parameters)) 
}
-- For each Parameter Type a declaration that every userData has at max one instance 
fact userDataMaxOnePosition {
all ud: UserData | no disj p1,p2: Position | ((p1 in ud.parameters) and (p2 in ud.parameters)) 
}
fact userDataMaxOneHeartBeat {
all ud: UserData | no disj hb1,hb2: HearthBeat | ((hb1 in ud.parameters) and (hb2 in ud.parameters))
}
fact userDataMaxOneBloodPressure {
all ud: UserData | no disj bp1,bp2: BloodPressure | ((bp1 in ud.parameters) and (bp2 in ud.parameters))
}
-- all request in the openSubscription list of a third party are owned by them and each of these req is accepted and subscribed
fact thirdPartyRequestOwnership {
all t: ThirdParty | all r: Request | ( r in t.openSubscription iff (r.owner = t and r.subType=SUB and r.status= Accepted))
}
-- DataSet exists only if there is a request that has them as content
fact dataSetExistance {
all d: DataSet | some r: Request | r.content = d
}
-- DataSet of Request has listerers only if the request is in a thirdParty openSubscription
fact ListenerOpenSubCoerence {
all ds: DataSet, r: Request, tp: ThirdParty | ( (r in tp.openSubscription) and (ds = r.content) ) iff ( tp in ds.listeners)
}
-- The same Third Party cannot do more than one request 

/** Dinamic Model **/

pred makeArequest [r: Request, tp: ThirdParty, t: SubscriptionType, s: Status, d: DataSet] {
r.owner = tp
r.subType = t
r.status = s
r.content = d
}
pred show {
(some u:User | #u.sources >=2) and
(some ds: DataSet | #ds.listeners > 0)
}

run show for 6 
run makeArequest
