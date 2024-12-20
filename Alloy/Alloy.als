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
--------------------------------
////////////PREDICATES/////////////////////
pred show{}

pred uploadInternship[c: Company, i: Internship] {
 //pre
i.status=notUploaded
//post
  c.upload'=c.upload+i'
  i.status' = free
#Complaint=0
}

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
}

pred interruptInternship[com:Complaint, i:Internship]{
//pre
com.referredTo=i
com.status=notHandled
i.status=ongoing

//post
i.status'=interrupted
i.candidates'=i.candidates
i.~internship'=none
i.interview'=i.interview
com.status'=Handled
com.referredTo'=com.referredTo
i.~internship.university.interrupt'=i.~internship.university.interrupt+i'
}

pred internshipStatusChange[i:Internship]{
i.status=notUploaded; i.status=free; i.status=ongoing; i.status=interrupted
#Internship=1
}

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
-------------------------------------------------------------------------------------------------
///////////FACTS////////////////

------INTERNSHIP STATUS------------------------
fact OnGoing{
always(all i:Internship| i.status=ongoing iff i.~internship!=none and i.candidates=none and i.interview=none)
}

fact NotUploaded{
always(all i:Internship| i.status=notUploaded implies i.candidates=none 
                                                                               and i.interview=none
                                                                                            and i.~internship=none
                                                                                                     and i.~upload=none)
}

fact Free{
always(all i:Internship| i.status=free implies i.~internship=none)
}

fact Interrupted{
always(all i:Internship| i.status=interrupted implies 
                                                  i.~internship=none and 
                                                                 i.candidates=none and
                                                                                  i.interview=none)
}

------------
///////////////COMPLAINT STATUS//////////////
fact NotSubmitted{
always(all com:Complaint| com.status=notSubmitted implies 
                                                                     com.referredTo=none and
                                                                                       com.~submit=none)
}

fact notHandled{
always(all com:Complaint| com.status=notHandled implies
                                                            (com.referredTo in com.~submit.internship or 
                                                                        com.referredTo   in com.~submit.upload) and
                                                                                                                  com.~submit!=none and 
                                                                                                                          com.referredTo.status=ongoing)
}

fact Handled{
always(all com:Complaint| com.status=Handled implies 
                                                     com.referredTo.status=interrupted and
                                                                        com.referredTo.~internship=none)
}

///////////////////////////////////
fact NoStrangeInternship{
always(no i:Internship| i.status!=notUploaded and i.~upload=none)
}

fact OneComplaintPerStudent{
always( all s:Student| #(s.submit)<2)
}

fact OnlyOneSubmitter{
always(all com:Complaint| lone u:User| com in u.submit)
}

fact ComplaintMustReferredToIfSubmitted{
always(all com:Complaint| com.status=Handled implies 
                                                (com.referredTo!=none and 
                                                                           com.referredTo.status=interrupted))
}

fact ComplaintMustReferredToIfSubmitted2{
always(all com:Complaint| com.status=notHandled implies 
                                                     (com.referredTo!=none and 
                                                                     com.referredTo.status=ongoing))
}

fact OneWorker{
always(all i:Internship|lone s:Student| i in s.internship)
}

fact InterruptOnlyHandled{
always(all i:Internship, com:Complaint |i.status=interrupted implies 
                                                                     i in com.referredTo and
                                                                                             com.status=Handled) 
                                                                                                                               
}

fact InterruptInterrupted{
always(all i:Internship|i in University.interrupt iff i.status=interrupted)
}

fact OneInternshipOneCompany{
always(all disj c1,c2: Company| #(c1.upload & c2.upload)<1)
}

fact ConditionToInterview{
always(all i:Internship| i.interview in i.candidates)
}

fact Interruption{
always(all i:Internship| i.status=ongoing and i.status'=interrupted implies
                                                                              i' in i.~internship.university.interrupt')
}

fact ConditionToSubmit{
always(all com: Complaint, i:Internship, c:Company| i in com.referredTo and c in i.~upload implies i in c.upload)
}

///////////////INTERNSHIP STATUS TRANSITION/////////////////////
fact InternshipStateChange1{
always(no i:Internship|i.status=notUploaded and (i.status'=ongoing or i.status'=interrupted))
}

fact InternshipStateChange2{
always(no i:Internship|i.status=free and (i.status'=notUploaded or i.status'=interrupted))
}

fact InternshipStateChange3{
always(no i:Internship|i.status=ongoing and (i.status'=free or i.status'=notUploaded))
}

fact InternshipStateChange4{
always(no i:Internship|i.status=interrupted and (i.status'=free or i.status'=notUploaded or i.status'=ongoing))
}
///////////////COMPLAINT STATUS TRANSITION/////////////////////
fact ComplaintStateChange1{
always(no com:Complaint|com.status=notSubmitted and com.status'=Handled)
}

fact ComplaintStateChange2{
always(no com:Complaint|com.status=notHandled and com.status'=notSubmitted)
}

fact ComplaintStateChange2{
always(no com:Complaint|com.status=Handled and (com.status'=notHandled or com.status'=notSubmitted))
}
//////////////ASSERTIONS/////////////////////////
assert noComplaintReferredToWrong{
always(all com:Complaint, u:User| (u in com.referredTo.~upload and u in Student implies u.internship in com.referredTo) or
                                                  (u in com.referredTo.~upload and u in Company implies u.upload in com.referredTo))
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
