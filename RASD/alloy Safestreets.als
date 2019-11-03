// this is the abstract general Category
abstract sig Category{}

//all the possible categories of user that extends Category
sig CarDriver extends Category{}
sig MotorCyclist extends Category{}
sig Pedestrian extends Category{}
sig Cyclist extends Category{}


abstract sig bool{}

one sig NotDisabled extends bool{}
one sig Disabled extends bool{}

sig string{}
sig fc{}
sig Email{}
sig date{}

// this is the accout of a single user
sig privateUser{
	name: one string,
	surname: one string,
	username:one string,
	password:one  string,
	cardriverChoice:lone  CarDriver,
	motorcyclistChoice: lone MotorCyclist,
	pedestrianChoice: lone Pedestrian,
	cyclistChoice:lone Cyclist,
	emailChoice:one  Email,
	fiscalcode:one  fc,
	dateofBirth: one date,
	drivelicensecode: lone string,
	disabledChoice:one  bool
}{
	name!=none and surname!=none and username!=none and password!=none and 
	cyclistChoice!=none  and emailChoice!=none and fiscalcode!=none and 	dateofBirth!=none and
	disabledChoice !=none and motorcyclistChoice!=none and cardriverChoice!=none and pedestrianChoice!=none
	and cyclistChoice!=none
}

/*Here we want to ensure that every possible string in our system is a field of at least on user account*/
fact everyStringLikenToUser{
	(all s:string |(some u:privateUser |u.name=s or u.surname=s or u.username=s
	or u.password=s))
}


/*Here we want to ensure that every possible category instance is related to at leat one user*/
fact allCtegoriesLinkedToUser{
	(all c:CarDriver |(some u:privateUser |u.cardriverChoice=c ))and
	(all m:MotorCyclist |(some u:privateUser |u.motorcyclistChoice=m ))and
	(all p:Pedestrian |(some u:privateUser |u.pedestrianChoice=p )) and
	(all c:Cyclist |(some u:privateUser |u.cyclistChoice=c ))
}

/*Here we want to ensure that each fc instance will be linked to one user*/
fact allFcLinkedToUser{
	(all f:fc |(some u:privateUser |u.fiscalcode=f )) 
}

/*here we want to ensure that every email instance in the model will be linked to at least one user*/
fact allEmailLinkedToUser{
	(all e:Email |(some u:privateUser |u.emailChoice=e )) 
}

/*here we want to ensure that every possible date will be linked to at least one user*/
fact allTheDataLinkedToUser{
		(all d:date|(some u:privateUser |u.dateofBirth=d )) 
}

/*Here we want to ensure that every category which can be disable or not is linked to at least one user*/
fact disableChoicesLinkedToUser{
	(all n:NotDisabled|(some u:privateUser |u.disabledChoice=n))and
	(all d:Disabled|(some u:privateUser |u.disabledChoice=d )) 
}

// ensure that 2 different account can't have the same username
fact notSameUserNames{
	no disj u1,u2:privateUser|u1.username=u2.username
}


// ensure that there are no account with the same fiscal code.
fact notSameFiscalCode{
	no disj u1,u2:privateUser | u1.fiscalcode=u2.fiscalcode
}

// ensure that there are not accounts with the same email.
fact notSameMail{
	no disj u1,u2: privateUser | u1.emailChoice=u2.emailChoice
}

pred show{}

run show for 10
	
