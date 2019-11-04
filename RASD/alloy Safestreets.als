// signatures for the fields of the users of the application
sig Date{}
sig Name{}
sig Surname{}
sig Username{}
sig Password{}
sig fc{}
sig Email{}
sig Drivelicense{}
abstract sig boolDisabled{}
sig Disabled extends boolDisabled{}
sig Notdisabled extends boolDisabled{} 

//this is the signature of the private user. It is abstract
abstract sig privateUser{
	name:one Name,
	surname:one  Surname,
	username:one Username,
	password:one  Password,
	fiscalcode:one fc,
	email:one  Email,
	dateofbirth: one Date
}

sig cardriver extends privateUser{
	disabledChoice:one boolDisabled,
	license:one Drivelicense
}

sig pedestrian extends privateUser{
	disabledChoice:one boolDisabled
}

sig motorcyclist extends privateUser{
		license: one Drivelicense
}

sig cyclist extends privateUser{}

/* here wa want to ensure that an email identifies a user in an unique way. It is also like this for the 
fiscal code  and the username*/
fact userIdentifiers{
   (no disj u1,u2:privateUser | u1.email=u2.email or u1.fiscalcode=u2.fiscalcode
	or  u1.username=u2.username)
}

// we ensure that the driving license can uniquely identify a motorcyclist or a carDriver
fact uniqueDrivingLicense{
	(no disj u1,u2:cardriver | u1.license=u2.license) and
	(no disj u3,u4:motorcyclist | u3.license=u4.license) and
    (no u5:cardriver,u6:motorcyclist | u5.license=u6.license)
}

/*Here we want to ensure that every instance of Name,Surname,Username,Password,fc,Email,Date,
Drivinglicense will be linked to at least one user.*/
fact everythingLinkedToUser{
	(all n:Name|(some u1:privateUser| u1.name=n))and
	(all su: Surname|(some u2:privateUser| u2.surname=su)) and
	(all us: Username|(some u3:privateUser |u3.username=us))and
	(all pa: Password|(some u4:privateUser | u4.password=pa)) and
	(all f: fc|(some u5:privateUser |u5.fiscalcode =f)) and
	(all em: Email|(some u6:privateUser |u6.email=em ))and
	(all d: Date|(some u7:privateUser | u7.dateofbirth=d)) 
}

fact DisabledInstancesLinkedToUser{
	(all b:boolDisabled |(some c1:cardriver| c1.disabledChoice = b ))or
	(all b1:boolDisabled |(some p1:pedestrian| p1.disabledChoice = b1 ))
}

fact drivingLicenseLinkedToUser{
	((all dr:Drivelicense|(some m:motorcyclist|m.license=dr)) or
	(all dr1:Drivelicense|(some cd:cardriver|cd.license=dr1)))
}

pred show{}

run show for 10 but 1 privateUser

