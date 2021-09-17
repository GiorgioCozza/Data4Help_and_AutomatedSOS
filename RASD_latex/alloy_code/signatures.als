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
	-- the timeout fixed for example to 30 seconds
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
	devices: set Device
}

sig Device{
	user: one User,
	healthParameters: set HealthIndicator,
	location: Location lone -> Time,
	supported: Bool one -> Time,
	registered: Bool one -> Time,
	connected: Bool one -> Time
}

sig FiscalCode{
	identify: lone User
}

sig HealthIndicator{}

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

sig Supervisor extends User{
	supervised: set User,
	
}

sig SupervisorRequest{
	receiver: one User,
	accepted: Bool one -> Time	
}

-- Notification sent to the Supervisor each time something anomalous happens to the supervised user
sig SupervisorNotification{
	supervisor: one Supervisor,
	reason: one Condition
}


-- An event that triggers an anomaly or emergency condition
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
