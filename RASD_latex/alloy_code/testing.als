-- D4H Testing

run isDeviceSupported for 5 but 3 Device, 3 Time, 1 User, 5 HealthIndicator, 1 Location, 3 Int
run isDeviceConnected for 5 but 3 Device, 3 Time, 1 User, 5 HealthIndicator, 1 Location, 3 Int
run makeRequest for 2 but 2 User, 2 ThirdParty, 2 Request, 2 Time
run acceptRequest for 2 but 1 User, 1 ThirdParty, 2 Request, 2 UserDataset, 2 Time
run rejectRequest for 2 but 1 User, 2 ThirdParty, 2 Request, 1 UserDataset, 2 Time
check userDatasetIsEmpty



-- ASOS Testing
run isEmergencyCondition for 3 but 3 User, 3 TriggerEvent, 3 Condition, 3 Time, 3 Int
run isRescueSquadAvailable for 3 but 1 ERM, 3 RescueSquad, 6 Time, 3 Int
run isTheNearestERM for 2 but 3 ERM
run isEmergencyCondition for 2 but 3 User, 6 TriggerEvent, 3 Condition, 3 EmergencyCondition
run ifEmergencyAlertERMAndDispatch for 2 but 3 User, 3 EmergencyCondition, 1 ERM, 3 RescueSquad, 3 Time, 3 Int
run addSupervisedUser for 2 but 3 User, 2 Supervisor
run notifySupervisor for 2 but 1 Supervisor, 2 User, 2 Condition, 2 SupervisorNotification
check emergencyTriggers

