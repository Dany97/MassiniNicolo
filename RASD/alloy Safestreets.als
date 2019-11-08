/*all the signature necessary to define the fundamentals ones with respect to the model*/
sig Date{} // a simple date
sig Name{} // a name of a person
sig Surname{}// a surname of a person
sig Username{}// a username of a person in the application
sig Password{}// the password 
sig fc{} //signature of the fiscal code
sig Email{}// this is a signature of an Email
sig Drivelicense{}// signature of the driving License
abstract sig boolDisabled{}
abstract sig bool{}
sig logged extends bool{} // a signature which is associated to the fact that a user is logged into the system
sig notLogged extends bool{}//a signature which is associated to the fact that a user is not logged into the system
sig Disabled extends boolDisabled{} // signature associated to the fact that a person is disabled
sig Notdisabled extends boolDisabled{}//signature associated to the fact that a person is not disabled
abstract sig dangerousBool{}
sig DangerousInGeneral extends dangerousBool{}//a signature that indicate that the street is considered as dangerous
sig NotDangerousInGeneral extends dangerousBool{}//a signature that indicate that the street is not considered as dangerous
sig Picture{} // a signature of a picture
sig City{} // a signature of a city
sig MunicipalityIdCode{} // this is a signature of a code associated to the identity of the municipality
sig Violationdescription{}// a signature associated to the description of the violation
sig HourViolation{}// a signature associated to the hour when the violation occurred.
sig LicensePlate{}// a signature of a license plate of a vehicle


/*This represent the data given by the municipality. This data is used to mine them in order to retrieve 
more detailed informations. This data is mined by Safestreets*/
sig MunicipalityDataAccidents{
	street:Street,
	hour: HourViolation,
	date: Date,
	licenseplate: LicensePlate
}


/*this is the signature of the private user. It is abstract because the instances are the categories of the
user*/
abstract sig privateUser{
	name:one Name,
	surname:one  Surname,
	username:one Username,
	password:one  Password,
	fiscalcode:one fc,
	email:one  Email,
	dateofbirth: one Date,
	islogged: one bool
}


/*A category of user that is a car driver. This signature contains also a "flag" that indicate if the user is 
disabled and the driving License*/
sig cardriver extends privateUser{
	disabledChoice:one boolDisabled,
	license:one Drivelicense
}

/*This is a category of user which is a pedestrian user.He/she can also be a disabled person or not. */
sig pedestrian extends privateUser{
	disabledChoice:one boolDisabled
}

/*This is the motorcyclist user. In this signature it is also included  his/her driving license*/
sig motorcyclist extends privateUser{
		license: one Drivelicense
}

/*This is the signature of the user of the municipality who have a code to identify the municipality and 
a password  to access his/her account. It is also present the city of which the user belongs*/
sig MunicipalityUser{
	city: one City,
	municipalityIdCode: one MunicipalityIdCode,
	password: one Password
}

/*Fake integer.It is necessary only to represent different numbers*/
sig integer{}

sig cyclist extends privateUser{}

/*This is latitude and longitude that determine a place*/
sig Place{
	latitude: one integer,
	longitude: one  integer
}

/*This signature represents a street with its city, its longitude and latitude and if it is considered dangerous or not*/
sig Street{
	city: one City,
	place: one Place,
	dangerousInGeneral:one  dangerousBool
}

/*This signatire represents a violation report. It includes: the date, the hour and the street related to the violation.
It also include the user who has reported the violation, the picture of the violation and the license plate of the vehicle related to the
violation.*/
sig violationReport{
	dateViolation: one Date,
	hour : one  HourViolation,
	description: one  Violationdescription,
	street: one  Street,
	user: one  Username,
	picture: one Picture,
	licenseplate: one LicensePlate
}

/*This contains all the streets of the same city that are considered dangerous. All the dangerous streets of  a city are contained in
this signature */
sig DangerousStreetsInCity{
	street: set Street,
	city:one City
}{
	(all s1,s2:Street | s1.city=s2.city and s1.city=city)and
	street.dangerousInGeneral=DangerousInGeneral
	#street>0
}	
/*This fact ensures that if a dangerous street exsists, then there must be a DangerousStreetsInCity that contains it with the same city*/
fact dangerousStreetsGroupExsistence{
	(all s:Street | (s.dangerousInGeneral=DangerousInGeneral) implies 
	(some dsc:DangerousStreetsInCity | s in dsc.street ))
}
/*This fact ensures the fact that there cannot exsist 2 DangerousStreetsInCity with the same city and the intersection of the streets of 2 different 
DangerousStreetsInCity is the empty set.  */
fact uniquenessOfDangerousStreetsInCity{
	(no disj dsc1,dsc2: DangerousStreetsInCity | dsc1.city=dsc2.city) and
	(all dsc1,dsc2:DangerousStreetsInCity | (dsc1!=dsc2)implies(dsc1.street & dsc2.street = none) )
}

// this implies that if 2 streets have the same longitude and latitude, then they are in the same city and they are the same city
fact notSameCoordDifferentCity{
	(all s1,s2:Street | (s1.place.latitude=s2.place.latitude and s1.place.longitude=s2.place.longitude) implies 
	(s1.city = s2.city and s1=s2))
}


/*This alloy function returns the average number of reports per street*/
fun averageNReportPerStreet[c:City]: one Int{
	div[#{r:violationReport|r.city=c} ,#{s:Street|s.city=c}]
}

/*This function returns the total number of reports in a street of a city*/
fun NReportInStreet[s:Street]: one Int{
	#{r:violationReport|r.street=s and r.street.city=s.city}
}

/*This alloy function returns true if the street is considered dangerous and false if not.
A street is considered dangerous iff the number of reporting in that street is 10% major than the average per street. If this condition holds, then
the street is considered as dangerous*/
fun IsStreetDangerous[s: Street]: one dangerousBool{
	{d:dangerousBool | (d=DangerousInGeneral) iff(mul[NReportInStreet[s],10]>mul[11, averageNReportPerStreet[s.city]])}
}

/*For each street this fact establishes if it is considered dangerous or not*/
fact dangerousnessOfStreet{
	(all s:Street |(s.dangerousInGeneral=IsStreetDangerous[s])) or
    (all s1:Street | (some dc:DangerousStreetsInCity |dc.street=s1)or
	(all s2:Street |(some mda:MunicipalityDataAccidents | mda.street=s2 )))
}


/*Here we want to ensure that latitude and longitude identify uniquely a street*/
fact positionStreet{
	(all s1,s2:Street|( (s1.place.latitude=s2.place.latitude and s1.place.longitude=s2.place.longitude)implies
	(s2=s1 and s1.place=s2.place)))and
	(all p1,p2:Place| (p1.latitude!=p2.latitude or p2.longitude!=p1.longitude)iff(p2!=p1))
}

/*Here we want to ensure that there is a 1 to 1 corrispondence between the city and the code related
to the municipality. This is like to say that the code related to the municipality identifies both the municipality itself
and the city of the municipality.*/
fact linkBetweenCityAndCode{
	(all mu1,mu2:MunicipalityUser|((mu1.city!=mu2.city)iff(mu1.municipalityIdCode!=mu2.municipalityIdCode)))
}

/*Here we want to ensure that there are not standalone city instance. In fact a city can be linked only to a MunicipalityUser or to a street.
A Municipality cannot be standalone and it can be linked only to MunicipalityUser. A password is linked to a MunicipalityUser.
In this fact we are also ensuring the fact that there are not standalone MunicipalityIdCode and Passwords. A password is linked
only to a MunicipalityUser or a privateUser and the MunicipalityIdCode is linked only to a MunicipalityUser*/
fact everythingLinkedToMunUsr{
	((all c:City|(some m1:MunicipalityUser| m1. city=c ))or
	(all c1:City|(some s:Street|  s.city=c1))or
	(all c2:City |(some  dc:DangerousStreetsInCity |dc.city=c2)))
	and (all m:MunicipalityIdCode|(some m2:MunicipalityUser|m2.municipalityIdCode=m))and
	(all p:Password|(some m2:MunicipalityUser|m2.password=p)or 
	(all p1:Password |(some u1:privateUser | u1.password=p1)))
}

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
	((all us: Username|(some u3:privateUser |u3.username=us))or
	(all us1: Username|(some v4:violationReport|v4.user=us1)))and
	(all pa: Password|(some u4:privateUser | u4.password=pa)) and
	(all f: fc|(some u5:privateUser |u5.fiscalcode =f)) and
	(all em: Email|(some u6:privateUser |u6.email=em ))and
	((all d: Date|(some u7:privateUser | u7.dateofbirth=d))or
	((all d1: Date|(some v:violationReport | v.dateViolation=d1)))or
	(all d2:Date | (some md: MunicipalityDataAccidents |md.date=d2) ))and
	(all b:bool|(some u8:privateUser|u8.islogged=b)) and
	(all p:Place|(some s:Street|s.place=p))and
	(all i:integer|(some p:Place|p.longitude=i or p.latitude=i))and
	(all h:HourViolation|(some v2:violationReport|v2.hour=h)or
	(all h1:HourViolation|(some mda:MunicipalityDataAccidents | mda.hour=h1)))and
	(all de:Violationdescription|(some v3:violationReport|v3.description=de))and
	(all p:Picture|(some v4:violationReport|v4.picture=p))and
	(all lp: LicensePlate|(some v5:violationReport| v5.licenseplate=lp)or
	(all p1:LicensePlate |(some mda:MunicipalityDataAccidents | mda.licenseplate=p1)))and
	(all dg:dangerousBool|(some std:Street|std.dangerousInGeneral=dg))
}

/*Here we want to ensure that every boolDisabled is associated to a pedestrian or a cardriver and it cannot be standalone.*/
fact DisabledInstancesLinkedToUser{
	(all b:boolDisabled |(some c1:cardriver| c1.disabledChoice = b ))or
	(all b1:boolDisabled |(some p1:pedestrian| p1.disabledChoice = b1 ))
}

/*Here we want to ensure that every drivingLicense instance will be linked to at least one motorcyclist or one 
Cardriver*/
fact drivingLicenseLinkedToUser{
	((all dr:Drivelicense|(some m:motorcyclist|m.license=dr)) or
	(all dr1:Drivelicense|(some cd:cardriver|cd.license=dr1)))
}

/*This are the predicates that allow to see some of the several possible static views of the alloy model. 
These are some of the possible static worlds:*/


pred showStaticViewOfUsers{
	#privateUser=2
	#MunicipalityUser=1
	#MunicipalityDataAccidents=0
	#violationReport=0
	#DangerousStreetsInCity=0
	#Street=0
}

pred showStaticViewOfViolationsAndStreets{
	#privateUser=0
	#MunicipalityUser=0
	#MunicipalityDataAccidents=2
	#violationReport =1
	#Street = 4
}

pred showStaticCompleteModel{
	#MunicipalityDataAccidents=1
	#violationReport =1
	#Street = 2
	#privateUser=1
	#MunicipalityUser=1
}



run showStaticViewOfUsers for 7
run showStaticCompleteModel for 4
run showStaticViewOfViolationsAndStreets for 4




