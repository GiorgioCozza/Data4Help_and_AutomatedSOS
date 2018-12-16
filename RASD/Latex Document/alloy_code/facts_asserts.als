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

-- no Supervisor can be Supervisor of him/herself
fact notMyOwnSupervisor{
	all sv: Supervisor | sv not in sv.supervised
}

-- each supervisor is notified if an emergency or anomaly occurs to the supervised user
fact notifySupervisor{

	all sv: Supervisor, u: User, c: Condition, sn: SupervisorNotification | (sn.supervisor = sv and sn.reason = c) iff ((u in sv.supervised) and (sn.reason = c))
}

-- An emergency is raised by a critical trigger event, or directly by the user (isCritical true), or when the timeout expires
assert emergencyTriggers{

	all c: Condition | all t,t': Time | all ac: AnomalyCondition | all ec: EmergencyCondition | c = ec iff (t'.seconds > t.seconds) and ((c.triggerEvents.criticality.t = False and c.triggerEvents.criticality.t' = True) and (ac.timeout.seconds = 0) and (ac.isCritical.t' = True))
}

