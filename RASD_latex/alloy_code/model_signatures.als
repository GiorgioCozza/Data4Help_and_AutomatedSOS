
-- MODEL SIGNATURES

module model_signatures

open util/integer
open util/boolean
open util/time


-- DATA4HELP


sig Location {
	--Latitude
	lat: one Int,
	--Longitude
	long: one Int
}{
	long >= -90 and long <= 90 and lat >= -180 and lat <= 180
}


sig Timer{
	seconds: one Int
}



sig User{
	dataset: lone UserDataset,
	pendingList: lone PendingRequests,
	devices: set Device
}



sig Device{
	user: lone User,
	healthParameters: set HealthIndicator,
	location: Location lone -> Time,
	supported: Bool one -> Time,
	registered: Bool one -> Time,
	connected: Bool one -> Time
}


sig FiscalCode{
	identify: lone User
}


sig HealthIndicator{
	
}


abstract sig Dataset{}

sig UserDataset extends Dataset{
	subject: one User,
	sensors: set Device,
	healthStatus: set HealthIndicator,
	userPosition: set Location
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
	requestObject: one UserDataset,
	userDecision: Bool one -> Time
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
	position: one Location,
	userDistance: one Int,
	squads: some RescueSquad,
	managedEmergencies: set EmergencyCondition
}{
	#squads > #managedEmergencies
	userDistance > 0
}

sig RescueSquad{
	position: one Location,
	userDistance: one Int,
	erm: one ERM,
	currentEmergency: EmergencyCondition lone -> Time,
	//introduced because a rescue squad could be unavailable not other reason as well as an emergency
	available: Bool one -> Time 							
}{
	-- a rescue squad is dispatched to an emergency only if available
	all t: Time | (available.t = True implies currentEmergency.t = none) and (currentEmergency.t != none implies available.t = False)

	all disj t',t: Time | currentEmergency.t != none implies (available.t' = False and currentEmergency.t' = currentEmergency.t) 
	userDistance > 0
}

sig Supervisor{
	supervised: set User,
	
}

sig TriggerEvent{
	indicators: some HealthIndicator,
	constraints: some Int,
	criticality: one Bool 
}


abstract sig Condition{
	user: one User,
	emPosition: one Location,
	triggerEvents: some TriggerEvent,
	time: one Time
}


sig AnomalyCondition extends Condition{
}{
	-- Anomaly conditions are all those conditions in which the trigger event is NOT critical
	all te: TriggerEvent | (te in triggerEvents) and (te.criticality = False)
}


sig EmergencyCondition extends Condition{
}{
	-- Emergency conditions are all those Anomaly conditions in which the trigger event is critical
	all te: TriggerEvent | (te in triggerEvents) and (te.criticality = True)
}




-- CONSTRAINTS D4H

-- FACTS

-- Devices of the same user cannot provide data of the same health indicator
fact userDevicesNoSameIndicator{	
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
fact mustInvolve1000AnonUsers{
	all ar: AnonymousRequest | all t: Time | ar.accepted.t = True iff #(ar.involvedUser) >= 1000
}


-- A specific-user request has a unique subject
fact oneRequesToOneUser{
	all r: Request | all disj u1, u2: User | r.requestObject.subject = u1 implies r.requestObject.subject != u2
}


-- a third party accesses to a UserDataset only if authorized
fact onlyAuthorizedAccess{
	all tp: ThirdParty, ds: UserDataset, rq: Request, t: Time |
	 (ds in tp.accessTo and ds.subject = rq.requestObject.subject) iff rq.accepted.t = True 
}


-- AUTOMATED SOS CONSTRAINTS

-- FACTS

fact squadDispatchedIfEmergency{
	
}










-- PREDICATES

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





-- D4H Testing
run isDeviceSupported for 5 but 3 Device, 3 Time, 1 User, 5 HealthIndicator, 1 Location
run isDeviceConnected for 5 but 3 Device, 3 Time, 1 User, 5 HealthIndicator, 1 Location
run registerDevice for 5 but 3 Device, 3 Time, 1 User, 5 HealthIndicator, 1 Location
run makeRequest for 5 but 2 User, 2 ThirdParty, 2 Request
run acceptRequest for 2 but 2 User, 1 ThirdParty, 2 Request, 1 Time



