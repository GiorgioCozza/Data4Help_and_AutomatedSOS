
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

	all ferm: ERM | nerm != ferm and nerm.userDistance < ferm.userDistance
}


-- As soon as an emergency condition is detected the ERM is alerted and a RescueSquad is dispatched
pred ifEmergencyAlertERMAndDispatch[u: User, te: TriggerEvent, c: Condition, ec: EmergencyCondition, nerm, nerm': ERM, t: Time, rs: RescueSquad]{
	
	isEmergencyCondition[u,te,c,ec,t]

	nerm'.userDistance = nerm.userDistance
	isTheNearestERM[nerm] iff nerm'.managedEmergencies = nerm.managedEmergencies + ec
	
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
