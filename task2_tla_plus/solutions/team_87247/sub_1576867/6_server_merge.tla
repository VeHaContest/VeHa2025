----MODULE 6_server_merge----
EXTENDS Naturals, Sequences

(*    ОПИСАНИЕ СПЕЦИФИКАЦИИ №6    *)

(* В этой спецификации мы добавляем действие Merge: скачивание изменений с
   сервера при наличии конфликтов, и rebase конфликтующей части локального лога
   поверх записей с сервера.

   Задание сложное, для его выполнение предлагается два варианта:
   1) Реализовать операторы DivergentIndex, ChangedLineAndValue, ChangedEntries
      и ApplyDivergence, пользуясь описанием поведения данных операторов,
      которые приведены в комментариях к ним. Действие Merge уже написано и
      вызывает оператор ApplyDivergence для корректной модификации состояния,
      нужно обратить внимание на то, как устроен этот вызов.
   2) Проигнорировать все заготовки вспомогательных операторов и готовое
      действие Merge и реализовать данный функционал самостоятельно.

   В обоих случаях решение должно удовлетворять всем сформулированным в
   спецификации инвариантам. При этом два инварианта, LogAlwaysGrows и
   LogIsBounded, будут нарушаться при правильном реализации Merge.
   Необходимо разобраться почему и исправить их.

   Если спецификация не будет завершена, то будет оцениваться насколько
   далеко и корректно получилось продвинуться в решении.

   Модифицировать текст спецификации можно только в местах, которые
   помечены текстом "INSERT YOU CODE HERE". Вносить изменения в прочие части
   можно только в случае, если вы нашли в приведенном коде ошибку.
 *)

CONSTANTS
    MAX_TEXT_LINES,
    MAX_USERS,
    MAX_LOG_SIZE

VARIABLES
    file,
    log

TEXT_LINES == 1..MAX_TEXT_LINES
INIT_VALUE == 1
\* У сервера идентификатор = 0
SERVER == 0
\* Обычные пользователи имеют ID >= 1
USERS == 1..MAX_USERS
\* Тут все участники, как сервер, так и пользователи
PARTICIPANTS == {SERVER} \union USERS
\** Для уникальной записи в файл
PRIMES == 
    <<2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107>>

UserId(u) ==
    PRIMES[u]

LineId(i) ==
    PRIMES[MAX_USERS + 1 + i]

NewFile(user, line_num) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    [file EXCEPT ![user][line_num] = @ * UserId(user) * LineId(line_num)]
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

LastLogEntry(user) ==
    log[user][Len(log[user])]

Modified(user) ==
    LastLogEntry(user).file /= file[user]

Write(user, line_num) ==
    /\ user \in USERS
    /\ line_num \in TEXT_LINES
    /\ Modified(user) = FALSE
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ file' = NewFile(user, line_num)
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)
    \* Ограничиваем возможность бесконечно делать write:
    \* если файл уже изменен, то мы можем только закоммитить изменение
    \* /\ Modified(user) = FALSE   Активирующим формулам лучше быть наверху
    /\ UNCHANGED <<log>>

NewLogEntry(user) ==
    [user |-> user, file |-> file[user]]

Commit(user) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ Modified(user) = TRUE
    /\ Len(log[user]) < MAX_LOG_SIZE
    /\ log' = [log EXCEPT ![user] = Append(@, NewLogEntry(user))]
    /\ UNCHANGED file
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

IsPrefixOf(seq1, seq2) ==
    /\ Len(seq1) \leq Len(seq2)
    /\ seq1 = SubSeq(seq2, 1, Len(seq1))

AbleToPush(user) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ log[SERVER] # log[user] \** нечего пушить если равны
    /\ IsPrefixOf(log[SERVER], log[user])
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

Push(user) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ AbleToPush(user)
    /\ log' = [log EXCEPT ![SERVER] = log[user]]
    /\ file' = [file EXCEPT ![SERVER] = LastLogEntry(user).file]
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

AbleToPull(user) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ log[SERVER] # log[user] \** нечего пуллить если равны
    /\ IsPrefixOf(log[user], log[SERVER])
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

Pull(user) ==
    /\ AbleToPull(user)
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ log' = [log EXCEPT ![user] = log[SERVER]]
    /\ file' = [file EXCEPT ![user] = file[SERVER]]
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

(*
log[user] = <<
    [file |-> <<1, 1, 1>>, user |-> 0]
    [file |-> <<2, 1, 1>>, user |-> 1]
    [file |-> <<2, 3, 1>>, user |-> 1]
    [file |-> <<2, 3, 5>>, user |-> 1]>>

log[SERVER] = <<
    [file |-> <<1, 1, 1>>, user |-> 0]
    [file |-> <<2, 1, 1>>, user |-> 1]
    [file |-> <<2, 1, 4>>, user |-> 2]
    [file |-> <<2, 5, 4>>, user |-> 2]>>

DivergentIndex(user) = 3

Возвращаем индекс первой записи в логе пользователя,
которая отличается от лога сервера под тем же индексом. *)

DivergentIndex(user) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
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
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

(* Данный оператор принимает на вход две соседние записи в логе одного
   пользователя. Благодаря инварианту DiffBetweenConsequentEntries мы знаем,
   что соседние записи отличаются только одной строкой. Данный оператор
   возвращает запись вида [line_num |-> ..., value |-> ...],
   где line_num хранит индекс отличающейся строки, а value - новое значение,
   записанное в данную стоку.

    file1 = <<1, 2, 3>>
    file2 = <<1, 5, 3>>
    ChangedLineAndValue(file1, file2) = [line_num |-> 2, value |-> 5] *)
\** Только для соседних файлов в логе
ChangedLineAndValue(file1, file2) ==
    LET ci == CHOOSE i \in TEXT_LINES: file1[i] /= file2[i] IN
        [line_num |-> ci, value |-> file2[ci]]

(* Данный оператор возвращает последовательность всех модификаций файла,
  которые конфликтуют с записями сервера (то есть начиная с некоторого
  DivergentIndex(user)), в следующем виде:
  <<[line_num |-> .., value |-> ...],
    [line_num |-> .., value |-> ...],
    ...>>

log[user] = <<
    [file |-> <<1, 1, 1>>, user |-> 0]
    [file |-> <<2, 1, 1>>, user |-> 1]
    [file |-> <<2, 3, 1>>, user |-> 1]
    [file |-> <<2, 3, 5>>, user |-> 1]>>

Если DivergentIndex(user) = 3, то

ChangedEntries(user) = <<
    [line_num |-> 2, value |-> 3],
    [line_num |-> 3, value |-> 5]

Для реализации потребуется вызовы операторов
DivergentIndex и ChangedLineAndValue, которые вы должны реализовать
отдельно выше.
*)
ChangedEntries(user) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    IF log[SERVER] = log[user]
    THEN << >>
    ELSE LET
        start == DivergentIndex(user)
        FileOf(i) == log[user][i+start-1].file
    IN
        [i \in 1..(Len(log[user])-start+1) |-> ChangedLineAndValue(FileOf(i-1), FileOf(i))]
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

RECURSIVE ApplyDivergence(_, _, _)
ApplyDivergence(user, new_log, changed_entries) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
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
        ELSE ApplyDivergence(
            user, 
            UpdateLog(new_log, user, Head(changed_entries)),
            Tail(changed_entries)
        )
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

\* Между сервером и клиентом есть расхождение, конфликт,
\* при этом на сервере есть новые изменения
AbleToMergeButNotPullOrPush(user) ==
    /\ AbleToPull(user) = FALSE
    /\ AbleToPush(user) = FALSE
    /\ \E i \in DOMAIN log[SERVER]:
            /\ i \in DOMAIN log[user]
            /\ log[user][i] /= log[SERVER][i]

\* В действии Merge мы берем лог изменения сервера и добавляем к нему
\* сверху все новые расходящиеся изменения, которые были у нас локально.
\* Таким образом история всегда будет линейной.
Merge(user) ==
    /\ user \in USERS
    /\ AbleToMergeButNotPullOrPush(user)
    /\ log' = [
        log EXCEPT ![user] = ApplyDivergence(
            user,
            log[SERVER],
            ChangedEntries(user))]
    \** была небольшая ошибка: Len(log[user]) вместо Len(log'[user])
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
\* Тут небольшое изменение: автором первой записи в логе становится сервер.
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


FileType == [TEXT_LINES -> Nat]
LogEntry == [user: PARTICIPANTS, file: FileType]

TypeOK ==
    /\ file \in [PARTICIPANTS -> FileType]
    /\ DOMAIN log = PARTICIPANTS
    /\ \A u \in PARTICIPANTS: \A i \in DOMAIN log[u]: i >= 1
    /\ \A u \in PARTICIPANTS: \A i \in DOMAIN log[u]: log[u][i] \in LogEntry

GLOBAL_MAX_LOG_SIZE == (MAX_LOG_SIZE-1)*MAX_USERS+1

\* Количество записей в логе ограничено некоторой константой и не может
\* быть превышено. ИСПРАВЬТЕ ЭТОТ ИНВАРИАНТ.
LogIsBounded ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    \/ \A u \in PARTICIPANTS: Len(log[u]) <= GLOBAL_MAX_LOG_SIZE
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

\* Если изменения в файле были добавлены в лог, то последняя запись лога
\* соответствует новому содержимому файла.
LastLogEntryIsFile ==
    \A u \in PARTICIPANTS: Modified(u) = FALSE => LastLogEntry(u).file = file[u]

\* Мы не можем повторно перезаписывать содержимое файла, если до этого не
\* добавили предыдущие изменения в лог.
WriteOnlyOnce ==
    \A u \in USERS: \E line_num \in TEXT_LINES:
        ENABLED Write(u, line_num) => ~(ENABLED Commit(u))

\* При штатном функционировании системы (см. fairness в документации TLA+)
\* мы всегда дойдем до момента, когда лог будет полностью заполнен.
\* ИСПРАВЬТЕ ЭТОТ ИНВАРИАНТ.
LogAlwaysGrows ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    \E n \in MAX_LOG_SIZE..GLOBAL_MAX_LOG_SIZE: 
        \A u \in PARTICIPANTS: <>(Len(log[u]) = n)
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

\* Каждая запись в логе пользователя отражает изменение в одной и только одной
\* строке файла. Не должно быть ситуации, когда любые две соседние записи
\* в логе отличались больше чем на одну строку.
DiffBetweenConsequentEntries ==
    \A u \in USERS: \A i \in DOMAIN log[u]: i + 1 \in DOMAIN log[u] =>
        \E line_num \in TEXT_LINES:
            /\ log[u][i].file[line_num] /= log[u][i + 1].file[line_num]
            /\ \A other_line_num \in TEXT_LINES: other_line_num /= line_num =>
                    log[u][i].file[other_line_num] = log[u][i + 1].file[other_line_num]

\* При штатном функционировании системы (см. fairness в документации TLA+)
\* если логи всех пользователей заполнены (действие Next не может быть
\* выполнено), то логи стали одинаковы и синхронизированы.
\* Другими словами, невозможна ситуация, в которой логи разных пользователей
\* расходятся настолько, что их синхронизация через сервер становится
\* невозможна.
LogsConverge ==
    ~(ENABLED Next) =>
        (\A u1 \in PARTICIPANTS, u2 \in PARTICIPANTS: log[u1] = log[u2])

\* Мы не должны иметь возможность сделать Pull, если можем сделать Push,
\* и наоборот.
PullOrPush ==
    /\ \A u \in USERS: ENABLED Pull(u) =>
            ~(ENABLED Push(u))
    /\ \A u \in USERS: ENABLED Push(u) =>
            ~(ENABLED Pull(u))


(* VVVV     INSERT YOU CODE HERE     VVVV *)

\* ОПЦИОНАЛЬНОЕ место для дополнительных инвариантов.

NoDirectChangesOnServer ==
    /\ ~Modified(SERVER)

\** Лог ограничен -> когда-то нельзя будет совершать коммиты
EventuallyUnableToCommit == 
    \A u \in USERS: <>[] ~(ENABLED Commit(u))

\** Сильная версия LogAlwaysGrows
LogReachesMaxLength ==
    \E n \in MAX_LOG_SIZE..GLOBAL_MAX_LOG_SIZE:
        \A u \in USERS: <>[](Len(log[u]) = n)

(* ^^^^     INSERT YOU CODE HERE     ^^^^ *)
====