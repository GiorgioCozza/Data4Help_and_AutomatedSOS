-- DATA4HELP Alloy Model 

module Data4HelpAlloy

open util/integer
open util/boolean
open util/time

open 




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


-- The same request cannot be sent to two different users
fact oneRequesToOneUser{
	all r: Request | all disj u1, u2: User | r.requestObject.subject = u1 implies r.requestObject.subject != u2
}


-- a third party accesses to a UserDataset only if authorized
fact onlyAuthorizedAccess{
	all tp: ThirdParty, ds: UserDataset, rq: Request, t: Time |
	 (ds in tp.accessTo and ds.subject = rq.requestObject.subject) iff rq.accepted.t = True 
}


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

-- user accept request
pred acceptRequest[u, u': User, r: Request, ds: UserDataset, t: Time, tp, tp': ThirdParty]{
	r.requestObject.subject = u
	r.accepted.t = True
	r.requestObject = ds
	tp'.accessTo = tp.accessTo + ds
	u'.pendingList.requests = u.pendingList.requests - r
	tp'.pendingList.requests = tp.pendingList.requests - r
}

-- user rejects request, the list is updated
pred rejectRequest[u, u': User, tp, tp': ThirdParty, r: Request, ds: UserDataset, t: Time]{
	r.requestObject.subject = u
	r.accepted.t = False
	r.requestObject = ds
	u'.pendingList.requests = u.pendingList.requests - r
	tp'.pendingList.requests = tp.pendingList.requests - r
}



run isDeviceSupported for 5 but 3 Device, 3 Time, 1 User, 5 HealthIndicator, 1 Location
run isDeviceConnected for 5 but 3 Device, 3 Time, 1 User, 5 HealthIndicator, 1 Location
run registerDevice for 5 but 3 Device, 3 Time, 1 User, 5 HealthIndicator, 1 Location
run makeRequest for 5 but 2 User, 2 ThirdParty, 2 Request
run acceptRequest for 2 but 2 User, 1 ThirdParty, 2 Request, 1 Time
