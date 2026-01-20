----MODULE solution----
EXTENDS Naturals, Sequences

CONSTANTS
    MAX_TEXT_LINES,
    MAX_USERS,
    MAX_LOG_SIZE

VARIABLES
    file,
    log

TEXT_LINES == 1..MAX_TEXT_LINES
INIT_VALUE == 1
SERVER == 0
USERS == 1..MAX_USERS
PARTICIPANTS == {SERVER} \union USERS
PRIMES == 
    <<2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107>>

UserId(u) ==
    PRIMES[u]

LineId(i) ==
    PRIMES[MAX_USERS + 1 + i]

NewFile(user, line_num) ==
    [file EXCEPT ![user][line_num] = @ * UserId(user) * LineId(line_num)]

LastLogEntry(user) ==
    log[user][Len(log[user])]

Modified(user) ==
    LastLogEntry(user).file /= file[user]

Write(user, line_num) ==
    /\ user \in USERS
    /\ line_num \in TEXT_LINES
    /\ Modified(user) = FALSE
    /\ file' = NewFile(user, line_num)
    /\ UNCHANGED log

NewLogEntry(user) ==
    [user |-> user, file |-> file[user]]

Commit(user) ==
    /\ Modified(user) = TRUE
    /\ Len(log[user]) < MAX_LOG_SIZE
    /\ log' = [log EXCEPT ![user] = Append(@, NewLogEntry(user))]
    /\ UNCHANGED file

IsPrefixOf(seq1, seq2) ==
    /\ Len(seq1) \leq Len(seq2)
    /\ seq1 = SubSeq(seq2, 1, Len(seq1))

AbleToPush(user) ==
    /\ log[SERVER] # log[user]
    /\ IsPrefixOf(log[SERVER], log[user])

Push(user) ==
    /\ AbleToPush(user)
    /\ log' = [log EXCEPT ![SERVER] = log[user]]
    /\ file' = [file EXCEPT ![SERVER] = LastLogEntry(user).file]

AbleToPull(user) ==
    /\ log[SERVER] # log[user]
    /\ IsPrefixOf(log[user], log[SERVER])

Pull(user) ==
    /\ AbleToPull(user)
    /\ log' = [log EXCEPT ![user] = log[SERVER]]
    /\ file' = [file EXCEPT ![user] = file[SERVER]]

DivergentIndex(user) ==
    LET 
        server_log == log[SERVER]
        user_log == log[user]
        Min(a, b) == IF a < b THEN a ELSE b
        min_length == Min(Len(server_log), Len(user_log))
    IN
        IF IsPrefixOf(server_log, user_log) /\ (Len(server_log) < Len(user_log))
        THEN Len(server_log) + 1
        ELSE CHOOSE i \in 1..min_length:
            /\ server_log[i].file # user_log[i].file 
            /\ \A j \in 1..(i-1): server_log[j].file = user_log[j].file 

ChangedLineAndValue(file1, file2) ==
    LET ci == CHOOSE i \in TEXT_LINES: file1[i] /= file2[i] IN
        [line_num |-> ci, value |-> file2[ci]]

ChangedEntries(user) ==
    IF log[SERVER] = log[user]
    THEN << >>
    ELSE LET
        start == DivergentIndex(user)
        FileOf(i) == log[user][i+start-1].file
    IN
        [i \in 1..(Len(log[user])-start+1) |-> ChangedLineAndValue(FileOf(i-1), FileOf(i))]

RECURSIVE ApplyDivergence(_, _, _)
ApplyDivergence(user, new_log, changed_entries) ==
    LET
        ChangeFile(target, changed_entry) == 
            [target EXCEPT ![changed_entry.line_num] = changed_entry.value]
        UpdateLog(old_log, changer, changed_entry) == 
            LET log_record == [
                user |-> changer, 
                file |-> ChangeFile(
                    old_log[Len(old_log)].file, 
                    changed_entry
                )
            ] IN Append(old_log, log_record)
    IN
        IF changed_entries = << >> 
        THEN new_log
        ELSE ApplyDivergence(user, UpdateLog(new_log, user, Head(changed_entries)), Tail(changed_entries))

AbleToMergeButNotPullOrPush(user) ==
    /\ AbleToPull(user) = FALSE
    /\ AbleToPush(user) = FALSE
    /\ \E i \in DOMAIN log[SERVER]:
            /\ i \in DOMAIN log[user]
            /\ log[user][i] /= log[SERVER][i]

Merge(user) ==
    /\ user \in USERS
    /\ AbleToMergeButNotPullOrPush(user)
    /\ log' = [
        log EXCEPT ![user] = ApplyDivergence(
            user,
            log[SERVER],
            ChangedEntries(user))]
    /\ file' = [file EXCEPT ![user] = log'[user][Len(log'[user])].file]

WriteAction ==
    \E user \in USERS, line_num \in TEXT_LINES:
        /\ Write(user, line_num)

CommitAction ==
    \E user \in USERS:
        Commit(user)

PushAction ==
    \E user \in USERS:
        Push(user)

PullAction ==
    \E user \in USERS:
        Pull(user)

MergeAction ==
    \E user \in USERS:
        Merge(user)

InitFile == [new_log \in TEXT_LINES |-> INIT_VALUE]
InitLog == <<[user |-> SERVER, file |-> InitFile]>>

Init ==
    /\ file = [u \in PARTICIPANTS |-> InitFile]
    /\ log = [p \in PARTICIPANTS |-> InitLog]

Next ==
    \/ WriteAction
    \/ CommitAction
    \/ PushAction
    \/ PullAction
    \/ MergeAction

vars == <<file, log>>
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

----

FileType == [TEXT_LINES -> Nat]
LogEntry == [user: PARTICIPANTS, file: FileType]

TypeOK ==
    /\ file \in [PARTICIPANTS -> FileType]
    /\ DOMAIN log = PARTICIPANTS
    /\ \A u \in PARTICIPANTS: \A i \in DOMAIN log[u]: i >= 1
    /\ \A u \in PARTICIPANTS: \A i \in DOMAIN log[u]: log[u][i] \in LogEntry

----

GLOBAL_MAX_LOG_SIZE == (MAX_LOG_SIZE-1)*MAX_USERS+1

LogIsBounded ==
    \/ \A u \in PARTICIPANTS: Len(log[u]) <= GLOBAL_MAX_LOG_SIZE

LastLogEntryIsFile ==
    \A u \in PARTICIPANTS: Modified(u) = FALSE => LastLogEntry(u).file = file[u]

WriteOnlyOnce ==
    \A u \in USERS: \E line_num \in TEXT_LINES:
        ENABLED Write(u, line_num) => ~(ENABLED Commit(u))

LogAlwaysGrows ==
    \E n \in MAX_LOG_SIZE..GLOBAL_MAX_LOG_SIZE: 
        \A u \in PARTICIPANTS: <>(Len(log[u]) = n)

(* Consequent entries should differ by only one line *)
DiffBetweenConsequentEntries ==
    \A u \in USERS: \A i \in DOMAIN log[u]: i + 1 \in DOMAIN log[u] =>
        \E line_num \in TEXT_LINES:
            /\ log[u][i].file[line_num] /= log[u][i + 1].file[line_num]
            /\ \A other_line_num \in TEXT_LINES: other_line_num /= line_num =>
                    log[u][i].file[other_line_num] = log[u][i + 1].file[other_line_num]

LogsConverge ==
    ~(ENABLED Next) =>
        (\A u1 \in PARTICIPANTS, u2 \in PARTICIPANTS: log[u1] = log[u2])

PullOrPush ==
    /\ \A u \in USERS: ENABLED Pull(u) =>
            ~(ENABLED Push(u))
    /\ \A u \in USERS: ENABLED Push(u) =>
            ~(ENABLED Pull(u))

NoDirectChangesOnServer ==
    /\ ~Modified(SERVER)

EventuallyUnableToCommit == 
    \A u \in USERS: <>[] ~(ENABLED Commit(u))

LogReachesMaxLength ==
    \E n \in MAX_LOG_SIZE..GLOBAL_MAX_LOG_SIZE:
        \A u \in USERS: <>[](Len(log[u]) = n)

====