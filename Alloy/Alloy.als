abstract sig User{
var submit: lone Complaint
}

sig Internship{
var candidates: set Student,
var status: InternshipStatus,
var worker: lone Student,
var uploadedBy: lone Company
}

enum InternshipStatus {notUploaded, free, ongoing, interrupted}

sig Company extends User{
var uploaded: set Internship,
}

sig Student extends User{
university: one University,
var internship: lone Internship,
}

sig University{
enrolledStudents: set Student
}

one sig Interview {
var participants: Internship -> Student  
}

sig Complaint{
var submittedBy: lone User,
var referredTo: lone Internship,
var status: ComStatus
}

enum ComStatus {notSubmitted,notHandled,Handled}
--------------
//FACTS

//if the internship is ongoing there should be a worker assigned and no more canidates
fact OnGoingNeedWorkerNoCandidates{
always(all i: Internship |  
                    i.status = ongoing iff (i.worker!=none and i.candidates=none ))
}

//correlation between uploaded of i by c
fact NoUploadedByNoUploaded{
always( all i:Internship, c:Company| 
                   c in i.uploadedBy iff i in c.uploaded) 
}

//if the internship isn't yet upload,it can't have uploadedBy
fact NoUpNoUploadedStatus{
always(all i:Internship| 
                    i.uploadedBy=none iff i.status=notUploaded)
}

//if the internship isn't yet uploaded, it can't have worker or candidates
fact NotUploaded{
always(all i:Internship| 
                   i.status=notUploaded implies i.candidates=none and i.worker=none)
}
--------------------
//STATUS MANAGERS

fact StateChanges{
always(all i:Internship| 
                   i.status=free and i.status'=ongoing implies 
                                  acceptCandidate[i.uploadedBy,i.worker',i])
}

fact StateChanges2{
always(all i:Internship| 
                   i.status=notUploaded and i.status'=free implies 
                                            publishInternship[i.uploadedBy',i])
}

fact StateChanges3{
always(all i:Internship, com:Complaint|
               (i in com.referredTo and i.status=ongoing and i.status'=interrupted) implies 
                                                                     interruptInternship[i.worker.university,com])
}

fact StateChanges4{
always(no i:Internship| (i.status=ongoing and i.status'=free) 
                             or (i.status=notUploaded and i.status'=ongoing) 
                            or (i.status=notUploaded and i.status'=interrupted)
                             or(i.status=free and i.status'=notUploaded))
}
-------

//correlation between students and relatives universities
fact CorrelationUniStu{
    always(all s: Student, u: University | 
        (s in u.enrolledStudents) iff (s.university = u))
}

//Correlation between worker and internship attributes
fact CorrelationWorkerIntern{
always (all i: Internship, s: Student| 
                (s in i.worker and i.status=ongoing) iff i in s.internship)
}

//The same internship cannot be published by two different companies.
fact NoSameInternship{
always(all disj c1,c2: Company| 
                   (c1.uploaded & c2.uploaded)=none)
}

//If a complaint reffred to an interrupted internship so interruptINternship happened
fact InterruptSoInterrupted{
always(all com: Complaint, i: Internship| 
                     (com.referredTo = i and i.status = interrupted) implies
                                            once interruptInternship[i.worker.university, com])
}

//Correlation between interrupted internship status and relative handled complaint
fact InterruptedHandled{
always(all com: Complaint, i: com.referredTo| 
                 i.status = interrupted iff com.status = Handled)
}

//Two user can't submit the same complaint
fact NoSameUserComplaint{
always(all disj u1,u2:User| #(u1.submit & u2.submit)<1)
}

//If there is an interview, it means the student has applied for that internship.
fact InterviewSoCandidate{
always( all s: Student, i: Internship | 
                      s in i.(Interview.participants) implies s in i.candidates)
}

//An unsubmitted complaint is empty.
fact Notsubmittednoattributes{ 
always(all com:Complaint| 
                  com.status=notSubmitted iff 
                                 (com.submittedBy=none and com.referredTo=none))
}

//There is no submitted complaint that is not related to an internship.
fact submittedButNotReferred{
always(no com: Complaint |
                   com.status != notSubmitted and com.referredTo = none)
}

//If the complaint is handled, the connection between the student and the internship must be terminated.
fact handledComplaint{
always(all com: Complaint| 
             com.status = Handled implies 
                      (com.referredTo.worker.internship = none and com.referredTo.worker = none))
}

//If the internship is interrupted, there are no longer any candidates or workers.
fact InterruptedSoNoMoreAvailable{
always(all i: Internship|
                 i.status = interrupted implies 
                            (i.candidates = none and i.worker=none))
}

//There is no student who submits a complaint about an internship for which they are not a worker.
fact WorkerSoSubmitCompliant{
always(no s: Student, com: Complaint, i: com.referredTo| 
                                       i.worker != s and com.submittedBy =s)  
}

//Complaint should referred to interrupted or ongoing internship
fact ComplaintSoINterruptedOrOngoing{
always(all com:Complaint, i: Internship | 
                           com.referredTo = i implies 
                                     (i.status=interrupted or i.status= ongoing))
}


//One complaint per student
fact OneComplaintPerStudent{
always(all s:Student| #s.submit<2)
}

//An complaint per company per internship
fact oneComplaintPerInternshipByCompany {
always(all c: Company, i: Internship | 
        lone com: Complaint | 
               com.referredTo = i and com.submittedBy = c)
}

//Student can submit a complaint only if he has that internship linked
fact ConditionToSubmitStudent{
always(all s:Student, com: Complaint|
                     s in com.submittedBy implies 
                                       com.referredTo = s.internship) 
}


//Complaints can only be submitted by copmany if it is your own internship.
fact ConditionToSubmitCompany{
always(all c:Company, com:Complaint| 
                            c in com.submittedBy implies 
                                   (com.referredTo in c.uploaded and com.referredTo.status=ongoing))
}

//An internship is interrupted only if there is a complaint in the "handled" state that concerns it.
fact InterruptedSoHandled{
always(all i: Internship| 
                   (i.status = interrupted) iff 
                         (some com: Complaint| com.referredTo = i and com.status = Handled))
}

//If a complaint is not handled it means that has been submitted
fact NosubmittedNoSubmittedBy{
always(all com:Complaint| 
           com.status=notHandled implies com.submittedBy!=none)
}

//if a students is a worker can't be also a candidate for other available internships
fact IfWorkerNoCandidate{
always(all s:Student, i:Internship|
                       s.internship!=none implies s not in i.candidates)  
}

//Define the rules for submitting a complaint by a student and by a company
fact SubmittedByReferred{
always(all com:Complaint,c:Company, s:Student| 
               s in com.submittedBy implies s.internship in com.referredTo or 
                                   c in com.submittedBy implies com.referredTo in c.uploaded)  
}

//Correlation between submit and submittedBy attributes
fact SubmittedByandSubmit{
always(all com:Complaint,u:User| 
            com in u.submit implies com.submittedBy=u)
}


//if the interhsip is free, it can't have worker
fact FreeNoWorker{
always(all i:Internship| i.status=free implies i.worker=none )
}

//Correlation between submit and submittedBy attributes
fact SubmittedByandSubmit{
always(all com:Complaint,u:User| 
            com in u.submit iff com.submittedBy=u)
}

---------------------------------------------------------------------
//PREDICATI

pred publishInternship[c: Company, i: Internship]{
//precond
i.status=notUploaded

//postcond
c.uploaded' = c.uploaded + i'
i.uploadedBy'=c'
i.candidates' = none
i.status' = free
}

pred apply[s:Student, i: Internship]{
//precond
s not in i.candidates
s.internship=none
i.status=free

//postcond
all i1:Internship|i1!=i implies i1.candidates'=i1.candidates
i.candidates'=i.candidates+s
i.status'=i.status
s.internship'=s.internship
#Student<2
#Complaint<2
#Internship<2
}


pred acceptCandidate[c: Company, s: Student, i: Internship]{
//precond
i in c.uploaded
s in i.candidates
s in i.(Interview.participants)
i.status = free
s.internship = none

//postcond
(all i1:Internship| s in i1.candidates implies s' not in i1.candidates')
(all i2: Internship | i2 != i implies (i2.candidates' = i2.candidates and i2.status' = i2.status))
i.candidates' = none
i.status' = ongoing
i.worker' = s'
s.internship'=i'
#Student<2
#Complaint<2
#Internship<2
}

pred scheduleInterview[c: Company, s: Student, i: Internship, inter: Interview] {
//precond
not (i->s) in inter.participants
i in c.uploaded
s in i.candidates
i.worker = none
s.internship = none
i.status = free

//postcond
inter.participants' =  inter.participants + (i->s)
s.internship' = s.internship
(all i1: Internship | i1 != i implies (i1.candidates' = i1.candidates and i1.status' = i1.status))
i.candidates' = i.candidates
i.worker' = i.worker
i.status' = i.status
c.uploaded' = c.uploaded
#Student<2
#Complaint<2
#Internship<2 
}

pred submitComplaint[com:Complaint, u:User, i:Internship]{
//precond
(u in i.worker or u in i.uploadedBy)
com.status=notSubmitted
com not in User.submit

//postcond
i'.status = i.status
com.referredTo'=i
com.submittedBy'=u'
u.submit'=com'
com.status'=notHandled
#Student<2
#Complaint<2
#Internship<2
}

pred interruptInternship[u: University, com: Complaint]{
//precond
com.referredTo.worker in u. enrolledStudents
com.referredTo.status = ongoing
com.status = notHandled

//postcond
com.referredTo.status' = interrupted
com.referredTo.worker.internship' = none
com.referredTo.worker' = none
com.referredTo' = com.referredTo
com.referredTo.uploadedBy' = com.referredTo.uploadedBy
com.status' = Handled
all i:Internship| i.candidates'=i.candidates and i.uploadedBy'=i.uploadedBy
#Student<2
#Complaint<2
#Internship<2
}



pred InternshipStateChanges[i:Internship]{
i.status=notUploaded; i.status=free;i.status=free; i.status=ongoing;i.status=ongoing; i.status=interrupted
#Student<2
#Complaint<2
#Internship<2
}


pred ComplaintStateChanges[com:Complaint]{
com.status=notSubmitted; com.status=notHandled; com.status=Handled
#Student<2
#Complaint<2
#Internship<2
}

pred show{}

run show
run publishInternship 
run apply 
run scheduleInterview 
run acceptCandidate 
run submitComplaint 
run interruptInternship 
run InternshipStateChanges
run ComplaintStateChanges 
-------------------------------------------
//ASSERTIONS

assert NoStudentOutOfUniversity{
 no s:Student |s.university=none
}
check NoStudentOutOfUniversity

assert InterruptesSoComplaintHandled{
no com:Complaint, i:Internship| i in com.referredTo and com.status=Handled and i.status!=interrupted
}
check InterruptesSoComplaintHandled

assert ComplaintNotSubmitted{
no com:Complaint| com.status=notSubmitted and com.referredTo!=none
}
check InterruptesSoComplaintHandled

assert InternshipNotUploaded{
no i:Internship| i.status=notUploaded and i.candidates!=none
}
check InternshipNotUploaded

assert InternshipOngoing{
no i:Internship| i.status=ongoing and i.candidates!=none and i.worker=none
}
check InternshipOngoing

assert submittedByReferredTo{
no com:Complaint| com.referredTo not in com.submittedBy.uploaded and 
                                              com.referredTo not in com.submittedBy.internship
}
check submittedByReferredTo
