-- SYSTEM ALLOY MODEL

open util/integer
open util/boolean

-- DATA4HELP

sig Time{
	seconds: one Int
}{
	seconds > 0
}

sig Timeout{
	seconds: one Int
}{
	seconds >= 0 and seconds <= 30
}

sig Location {
	--Latitude
	lat: one Int,
	--Longitude
	long: one Int
}{
	long >= -90 and long <= 90 and lat >= -180 and lat <= 180
}


sig User{
	dataset: lone UserDataset,
	pendingList: lone PendingRequests,
	devices: set Device,
	fiscalCode: one FiscalCode
}



sig Device{
	user: one User,
	healthParameters: set HealthIndicator,
	location: Location lone -> Time,
	supported: Bool one -> Time,
	registered: Bool one -> Time,
	connected: Bool one -> Time
}


sig FiscalCode{}


sig HealthIndicator{
	
}

abstract sig Dataset{}

sig UserDataset extends Dataset{
	subject: one User,
	// device registered to the service may change along the timeline
	sensors: Device some -> Time,
	// health data provided by previous registered devices must be included in the dataset
	healthStatus: HealthIndicator some -> Time,
	userPosition: set Location
}{
	--All the devices associated to the dataset are registered
	all d: Device, t: Time | d in sensors.t iff d.registered.t = True
	--No health data is provided to the system at time t, if the corresponding device is not registered
	all h: HealthIndicator, d: Device, t: Time | ((h in healthStatus.t) and (h != none) and (h in d.healthParameters) and (d in sensors.t)) iff d.registered.t = True
}


sig AnonymousDataset extends Dataset{
	involvedUsers: set User,
	healthStatus: set HealthIndicator 
}


sig ThirdParty{
	requests: set Request,
	accessTo: set UserDataset
}


sig Request{
	accepted: Bool one -> Time,
	requestor: one ThirdParty,
	requestObject: one UserDataset
}


sig PendingRequests{
	requests: set Request
}


sig AnonymousRequest{
	accepted: Bool one -> Time,
	involvedUser: one Int,
	requestor: lone ThirdParty,
	requestObject: lone AnonymousDataset,
}


-- AUTOMATED SOS


sig ERM{
	userDistance: one Int,
	squads: some RescueSquad,
	managedEmergencies: set EmergencyCondition
}{
	#squads >= #managedEmergencies
	userDistance > 0
}

sig RescueSquad{
	userDistance: one Int,
	erm: one ERM,
	//it determines if the rescue squad is dispatched for an emergency 
	currentEmergency: EmergencyCondition lone -> Time,
	//a rescue squad could be unavailable for other reasons as well as an emergency
	available: Bool one -> Time 							
}{
	-- a rescue squad is dispatched to an emergency only if available
	all t: Time | (currentEmergency.t != none implies available.t = False) and (available.t = True implies currentEmergency.t = none) 
	userDistance > 0
}


sig Supervisor{
	supervised: set User,
	notifications: set SupervisorNotification
}


sig SupervisorRequest{
	receiver: one User,
	accepted: Bool one -> Time	
}


sig SupervisorNotification{
	supervisor: some Supervisor,
	reason: one Condition
}


sig TriggerEvent{
	indicators: some HealthIndicator,
	constraints: some Int,
	criticality: Bool one -> Time
}


abstract sig Condition{
	user: one User,
	emPosition: lone Location,
	triggerEvents: some TriggerEvent,
}


sig AnomalyCondition extends Condition{
	timeout: one Timeout,
	//it is triggered by the user and determines if the detection is a false positive (false)
	// or an emergency (true)
	isCritical: Bool one -> Time
}{
	-- Anomaly conditions are all those conditions in which the trigger event is NOT critical
	all te: TriggerEvent, t: Time | (te in triggerEvents) and (te.criticality.t = False)
}


sig EmergencyCondition extends Condition{
	
}{
	-- Emergency conditions are all those Anomaly conditions in which the trigger event is critical
	all te: TriggerEvent, t: Time | (te in triggerEvents) and (te.criticality.t = True)
}




-- DATA4HELP FACTS AND ASSERTS

-- Devices of the same user cannot provide data of the same health indicator
fact noSameIndicator{	
	all disj d1, d2: Device | d1.user = d2.user implies d1.healthParameters != d2.healthParameters
}

-- The device can be registered only if connected and supported by the system
fact registeredIfSupported{
	all d: Device | all t: Time | d.registered.t = True implies d.supported.t = True and d.connected.t = True
}

-- One UserDataset cannot be associated to two different users
fact oneUserToOneDataset{
	all disj ds1, ds2: UserDataset | ds1.subject != ds2.subject 
}

-- If the anonymous request does not involve at least 1000 users 
fact only1000AnonUser{
	all ar: AnonymousRequest | all t: Time | ar.accepted.t = True iff #(ar.involvedUser) >= 1000
}

-- A specific-user request has a unique subject
fact oneRequestToOneUser{
	all r: Request | all disj u1, u2: User | r.requestObject.subject = u1 implies r.requestObject.subject != u2
}

-- a third party accesses to a UserDataset only if authorized
fact onlyAuthorizedAccess{
	all tp: ThirdParty, ds: UserDataset, rq: Request, t: Time |
	 (ds in tp.accessTo and ds.subject = rq.requestObject.subject) iff rq.accepted.t = True 
}

-- a user dataset is empty of health data if no device has never been registered
assert userDatasetIsEmpty{

	all ud: UserDataset, t,t': Time | (t'.seconds > t.seconds) and (ud.sensors.t' = none) implies (ud.healthStatus.t = none)

	
}




-- AUTOMATED SOS FACTS AND ASSERTS

-- the nearest ERM to the user position is always alerted
fact theNearestERMisAlerted{
	
	no erm: ERM | one erm': ERM | all ec: EmergencyCondition | ec in erm'.managedEmergencies iff ((erm' != erm) and (erm'.userDistance > erm.userDistance))
}

 -- For safety reasons could never happen that an EmergencyCondition is turned into an AnomalyCondition
fact emergencyNotTurnIntoAnomaly{
	
	all t, t': Time | no c: Condition | (t'.seconds > t.seconds and c.triggerEvents.criticality.t = True) and c.triggerEvents.criticality.t' = False
}

-- if an anomaly is detected this is turned into an emergency either if the user triggers the emergency or the timeout expires
fact emergencyTriggeredByAnomaly{

	all t: Time, c: Condition, ac: AnomalyCondition, ec: EmergencyCondition | c = ec iff ((ac.timeout.seconds = 0) or (ac.isCritical.t = True))
}

-- each supervisor is notified if an emergency or anomaly occurs to the supervised user
fact notifySupervisor{

	all sv: Supervisor, u: User, c: Condition,  sn: SupervisorNotification | sv in sn.supervisor iff ((u in sv.supervised) and (c.user = u))
}

-- An emergency is raised by a critical trigger event, or directly by the user (isCritical true), or when the timeout expires
assert emergencyTriggers{

	all c: Condition | all t,t': Time | all ac: AnomalyCondition | all ec: EmergencyCondition | c = ec iff (t'.seconds > t.seconds) and ((c.triggerEvents.criticality.t = False and c.triggerEvents.criticality.t' = True) and (ac.timeout.seconds = 0) and (ac.isCritical.t' = True))
}



-- DATA4HELP PREDICATES

-- the device is supported by the system
pred isDeviceSupported[d: Device, t: Time]{
	d.supported.t = True
}


-- the device is connected to the master device
pred isDeviceConnected[d: Device, t: Time]{
	d.connected.t = True
}

-- register a device in the system
pred registerDevice[us: one User, d: Device, h: HealthIndicator, t: Time]{
	isDeviceSupported[d,t]
	isDeviceConnected[d,t]
	d.user =  us
	d.healthParameters = h
	d.registered.t = True 
}

-- create a third party request
pred makeRequest[u: User, tp: ThirdParty, r:Request, t: Time, pr, pr': PendingRequests]{
	r.requestor = tp
	r.requestObject.subject = u
	pr'.requests = pr.requests + r
}

-- user accept request and the request is removed from the pending list
pred acceptRequest[u, u': User, r: Request, ds: UserDataset, t: Time, tp, tp': ThirdParty]{
	r.requestObject.subject = u
	r.accepted.t = True
	r.requestObject = ds
	tp'.accessTo = tp.accessTo + ds
	u'.pendingList.requests = u.pendingList.requests - r
}

-- user rejects request and the request is removed from the pending list
pred rejectRequest[u, u': User, tp: ThirdParty, r: Request, ds: UserDataset, t: Time]{
	r.requestObject.subject = u
	r.accepted.t = False
	r.requestObject = ds
	u'.pendingList.requests = u.pendingList.requests - r
}






-- AUTOMATED SOS PREDICATES

-- the system detects an emergency condition
pred isEmergencyCondition[u: User, te: set TriggerEvent, c: Condition, ec: EmergencyCondition, t: Time]{
	
	c.user = u
	c.triggerEvents = te
	te.criticality.t = True
	c = ec
}

-- the RescueSquad is available if an intervention is requested
pred isRescueSquadAvailable[erm: ERM, rs: RescueSquad, t: Time]{

	rs in erm.squads
	rs.available.t = True
	rs.currentEmergency.t = none
}

-- the alerted ERM is the nearest
pred isTheNearestERM[nerm: ERM]{

	no ferm: ERM | nerm = ferm and (nerm.userDistance > ferm.userDistance)
}

-- As soon as an emergency condition is detected the ERM is alerted and a RescueSquad is dispatched
pred ifEmergencyAlertERMAndDispatch[u: User, te: TriggerEvent, c: Condition, ec: EmergencyCondition, nerm, nerm': ERM, t: Time, rs: RescueSquad]{
	
	isEmergencyCondition[u,te,c,ec,t]

	nerm'.userDistance = nerm.userDistance
	isTheNearestERM[nerm]
 	nerm'.managedEmergencies = nerm.managedEmergencies + ec
	
	isRescueSquadAvailable[nerm',rs,t]
	rs.currentEmergency.t = ec implies rs.available.t = False
}

-- a supervised user accept the request of a Supervisor
pred addSupervisedUser[sv, sv': Supervisor, u: User]{
	
	sv'.supervised = sv.supervised + u
}

-- Notify the supervisor 
pred notifySupervisor[sv: Supervisor, u: User, sn: SupervisorNotification, c: Condition]{

	//precondition
	u in sv.supervised
	sn.reason = c
	c.user = u
	sn.supervisor = sv
}


-- D4H Testing

run isDeviceSupported for 5 but 3 Device, 3 Time, 1 User, 5 HealthIndicator, 1 Location, 3 Int
run isDeviceConnected for 5 but 3 Device, 3 Time, 1 User, 5 HealthIndicator, 1 Location, 3 Int
run makeRequest for 2 but 2 User, 2 ThirdParty, 2 Request, 2 Time
run acceptRequest for 2 but 1 User, 1 ThirdParty, 2 Request, 2 UserDataset, 2 Time
run rejectRequest for 2 but 1 User, 2 ThirdParty, 2 Request, 1 UserDataset, 2 Time
check userDatasetIsEmpty



-- ASOS Testing
run isEmergencyCondition for 2 but 2 User, 3 TriggerEvent, 3 Condition, 3 Time
run isRescueSquadAvailable for 2 but 1 ERM, 3 RescueSquad, 6 Time
run isTheNearestERM for 2 but 3 ERM
run ifEmergencyAlertERMAndDispatch for 2 but 1 User, 1 EmergencyCondition, 1 ERM, 1 RescueSquad, 1 Time
run addSupervisedUser for 2 but 3 User, 2 Supervisor
run notifySupervisor for 2 but 1 Supervisor, 2 User, 2 Condition, 2 SupervisorNotification
check emergencyTriggers


