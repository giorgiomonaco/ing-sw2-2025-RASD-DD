------------------------------------------------------------
////////////////SIGNATURES////////////////
------------------------------------------------------------
abstract sig User{
var submit: lone Complaint
}

sig Internship{
var candidates: set Student,
var status: InternshipStatus,
var interview:set Student
}

enum InternshipStatus {notUploaded,free, ongoing, interrupted}

sig Company extends User{
var upload: set Internship
}

sig Student extends User{
university: one University,
var internship: lone Internship
}

sig University{
var interrupt:set Internship
}


sig Complaint{
var referredTo: lone Internship,
var status: ComStatus
}

enum ComStatus {notSubmitted,notHandled,Handled}
------------------------------------------------------------
////////////////PREDICATES////////////////
------------------------------------------------------------
//One possible World
pred show{}

//In this world we can observe the creation of the internship by a company 
pred uploadInternship[c: Company, i: Internship]{
 //pre
i.status=notUploaded
//post
  c.upload'=c.upload+i'
  i.status' = free
#Complaint=0
}


//In this world we can observe a student applying for an internship
pred apply[s:Student,i:Internship]{
//pre
s not in i.candidates
s.internship=none
i.status=free
//post
i.~upload'=i.~upload
i.candidates'=i.candidates+s'
i.status'=free
s.internship'=none
#Complaint=0
}



//In this world we can observe a company scheduling an interview with a candidate
pred scheduleInterview[s:Student, i:Internship]{
//pre
s not in i.interview
s in i.candidates
s.internship=none
i.status=free
//post
i.~upload'=i.~upload
i.status'=i.status
i.interview'=i.interview+s'
s.internship'=s.internship
i.candidates'=i.candidates
#Complaint=0
}

//In this world we can observe a company accepting a candidate after an interview
pred acceptCandidate[s:Student, i:Internship]{
//pre
s in i.candidates
s in i.interview
//post
i.~upload'=i.~upload
i.status'=ongoing
s.internship'=i
i.candidates'=none
i.interview'=none
#Complaint=0
}

//In this world we can observe a user submitting a complaint about his ongoing internship
pred submitComplaint[com:Complaint, u:User, i:Internship]{
//pre
com.status=notSubmitted
i in u.internship or i in u.upload
i.status=ongoing


//post
i.status'=i.status
com.referredTo'=i
com.status'=notHandled
u.submit'=u.submit+com
#Complaint=1
}

//In this world we can observe an university interrupting an internship of one of his students after
//receiving a complaint by one of the interested parts
pred interruptInternship[i:Internship]{
//pre
i.~referredTo!=none 
some com:Complaint|i in com.referredTo and com.status=notHandled
i.status=ongoing
//post
i.status'=interrupted
i.~internship.university.interrupt'=i.~internship.university.interrupt+i'
}


//In this world we can observe the evolution of a complaint's status
pred internshipStatusChange[i:Internship]{
i.status=notUploaded; i.status=free; i.status=ongoing; i.status=interrupted
#Internship=1
}

//In this world we can observe the evolution of a internship's status
pred complaintStatusChange[com:Complaint]{
com.status=notSubmitted; com.status=notHandled; com.status=Handled
#Complaint=1
}







run show
run uploadInternship
run apply
run scheduleInterview
run acceptCandidate
run submitComplaint
run interruptInternship 
run internshipStatusChange
run complaintStatusChange
------------------------------------------------------
////////////////FACTS////////////////
------------------------------------------------------


---------------INTERNSHIP STATUS---------------
//Conditions to be satisfied to be an ongoing internship
fact OnGoing{
always(all i:Internship|
            i.status=ongoing iff
                i.~internship!=none and 
                         i.candidates=none and 
                                       i.interview=none)
}

//Conditions to be satisfied to be a NotUploaded internship
fact NotUploaded{
always(all i:Internship|
            i.status=notUploaded implies
                                 i.candidates=none 
                                         and i.interview=none
                                              and i.~internship=none
                                                      and i.~upload=none)
}

//Conditions to be satisfied to be a free internship
fact Free{
always(all i:Internship| 
                      i.status=free implies 
                                 i.~internship=none)
}

//Conditions to be satisfied to be an interrupted internship
fact Interrupted{
always(all i:Internship| 
            i.status=interrupted implies
                       i.~internship=none and 
                                i.candidates=none and
                                         i.interview=none and
                                             i.~referredTo.status=Handled)
}

---------------COMPLAINT STATUS---------------
//Conditions to be satisfied to be a NotSubmitted complaint
fact NotSubmitted{
always(all com:Complaint| 
            com.status=notSubmitted implies
                               com.referredTo=none and
                                                      com.~submit=none)
}

//Conditions to be satisfied to be a NotHandled complaint
fact notHandled{
always(all com:Complaint| 
            com.status=notHandled implies
                      com.referredTo!=none and
                         (com.referredTo in com.~submit.internship or 
                                 com.referredTo   in com.~submit.upload) and
                                                                com.~submit!=none and
                                                                   com.referredTo.status=ongoing)
}

//Conditions to be satisfied to be a Handled complaint
fact Handled{
always(all com:Complaint|
        com.status=Handled implies 
            com.referredTo!=none and
                 (com.referredTo in com.~submit.internship or 
                      com.referredTo   in com.~submit.upload) and
                                                      com.~submit!=none and 
                                                       (com.referredTo.status=ongoing or
                                                          com.referredTo.status=interrupted))
}

---------------GENERAL FACTS---------------

//Correlation between upload and internship status
fact NoStrangeInternship{
always(no i:Internship|
            i.status!=notUploaded and 
                              i.~upload=none)
}

//Imposing one complaint per student
fact OneComplaintPerStudent{
always( all s:Student| #(s.submit)<2)
}

//A complaint should have at most one submitter
fact OnlyOneSubmitter{
always(all com:Complaint| lone u:User| com in u.submit)
}

//An in ternship should have at most one worker
fact OneWorkerPerInternship{
always(all i:Internship|lone s:Student| i in s.internship)
}

//Correlation between internship status and complaint status
fact InterruptOnlyHandled{
always(all i:Internship, com:Complaint |
            i.status=interrupted and
                  i in com.referredTo implies 
                                 com.status=Handled)               
}

//If an internship is interrupted so once interruptInternship happened
fact InterruptedOnceInterrupt{
always(all i:Internship|(i in University.interrupt or 
                                           i.status=interrupted) implies 
                                                            once interruptInternship[i])
}

//Correlation between universities and internship status
fact UniInterrupt{
always(all i:Internship|i.~interrupt!=none iff i.status=interrupted)
}

//An internship can be uploaded by only one company
fact OneCompanyPerInternship{
always(all disj c1,c2: Company| #(c1.upload & c2.upload)<1)
}

//A student,in order to be interviewed, should be a candidate for that internship 
fact ConditionToInterview{
always(all i:Internship| i.interview in i.candidates)
}

//Correlation between the evolution of internship status and university's interruption
fact Interruption{
always(all i:Internship| 
            i.status=ongoing and 
                 i.status'=interrupted implies
                   i' in i.~internship.university.interrupt')
}

//Condition to satisfy by a company in order to submit
fact ConditionToSubmitC{
always(all com: Complaint, i:Internship, c:Company|
                                         i in com.referredTo and 
                                               com in c.submit implies
                                                                    i in c.upload)
}

//Condition to satisfy by a student in order to submit
fact ConditionToSubmitS{
always(all com: Complaint, i:Internship, s:Student| 
                            i in com.referredTo and 
                                    com in s.submit  implies 
                                                       s.internship=i)
}

//A worker can't be a candidate
fact WorkerNoCandidate{
always(all s:Student| s.internship!=none implies s.~candidates=none)
}

---------------INTERNSHIP STATUS TRANSITION---------------

fact InternshipStateChange1{
always(no i:Internship|i.status=notUploaded and 
                          (i.status'=ongoing or i.status'=interrupted))
}

fact InternshipStateChange2{
always(no i:Internship|i.status=free and 
               (i.status'=notUploaded or i.status'=interrupted))
}

fact InternshipStateChange3{
always(no i:Internship|i.status=ongoing and 
                      (i.status'=free or i.status'=notUploaded))
}

fact InternshipStateChange4{
always(no i:Internship|i.status=interrupted and 
            (i.status'=free or i.status'=notUploaded or i.status'=ongoing))
}





---------------COMPLAINT STATUS TRANSITION---------------

fact ComplaintStateChange1{
always(no com:Complaint|
                 com.status=notSubmitted and 
                                   com.status'=Handled)
}

fact ComplaintStateChange2{
always(no com:Complaint|
                 com.status=notHandled and 
                              com.status'=notSubmitted)
}

fact ComplaintStateChange2{
always(no com:Complaint|
                  com.status=Handled and 
                     (com.status'=notHandled or com.status'=notSubmitted))
}

---------------PERMANENT CONDITIONS---------------

fact SubmitterAlwaysSubmitter{
all u:User, com:Complaint| 
          com in u.submit implies
                        always(com in u.submit)
}

fact UploaderAlwaysUploader{
all c:Company, i:Internship|
                      i in c.upload implies 
                               always(i in c.upload)
}

fact ReferredAlwaysReferred{
all com:Complaint, i:Internship| 
                       com.referredTo=i implies 
                             always(com.referredTo=i)
}

fact InterruptedAlwaysinterrupted{
always(all u:University| u.interrupt in u.interrupt')
}
------------------------------------------------------------
////////////////ASSERTIONS////////////////
------------------------------------------------------------
assert noComplaintReferredToWrong{
always(all com:Complaint, u:User| 
      (u in com.referredTo.~upload and u in Student implies 
                                       u.internship in com.referredTo) or
             (u in com.referredTo.~upload and u in Company implies 
                                                         u.upload in com.referredTo))
}
check noComplaintReferredToWrong

assert  OneComplaintOneSubmitter{
always( no disj u1,u2:User| #(u1.submit & u2.submit)>1)
}
check OneComplaintOneSubmitter

assert  OneInternshipOneSubmitter{
always( no disj c1,c2:Company| #(c1.upload & c2.upload)>1)
}
check OneInternshipOneSubmitter

