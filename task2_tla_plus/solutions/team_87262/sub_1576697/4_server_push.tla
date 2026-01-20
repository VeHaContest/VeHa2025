----MODULE 4_server_push----
EXTENDS Naturals, Sequences

(*    ОПИСАНИЕ СПЕЦИФИКАЦИИ №4    *)

(* В этой спецификации мы добавляем сервер: специальный пользователь с id = 0,
   который будет использоваться для централизованной синхронизации логов между
   различными пользователями. У сервера есть собственная версия лога и файл,
   однако, в отличии от прочих пользователей, сервер не может самостоятельно
   выполнять никакие действия, он только реагирует на запросы о синхронизации.

   В задании нужно сделать следующее:
   1) Вставить части оператора NewFile, действий  Write и Commit, реализованные
      в предыдущей спецификации.
   2) Сформулировать свойство отсутствия конфликтов, которое позволит выполнять
      действие Push. Заметьте, что конфликты в спецификации возможны, их
      разрешением мы займемся в последующих спецификациях, где нужно будет
      реализовать действия Pull и Merge.
   3) Реализовать тело оператора AbleToPush и действие Push.

   AbleToPush должен удовлетворять следующим требованиям:
   1) Проверять, что при выполнении Push не перезапишутся никакие записи в логе
      сервера, которые там присутствуют.
   2) Проверить, что действие Push не нарушит никаких инвариантов.

   Push должен удовлетворять следующим требованиям:
   1) Результат операции: лог сервера и некоторого пользователя User становятся
      одинаковы (синхронизированы) за счет отправки изменений на сервер.
      Что значит отправка?
   2) Не забыть про локальную копию файла. Что с ней нужно сделать и где?

   Проверить корректность спецификации запуском TLC. Если инструмент находит
   ошибку, нужно разобраться, какое из сформулированных в спецификации условий
   нарушается и как это можно исправить.

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

NewFile(user, line_num) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    [l \in TEXT_LINES |-> IF l = line_num 
                          THEN file[user][line_num] * line_num * user
                          ELSE file[user][l]]
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

LastLogEntry(user) ==
    log[user][Len(log[user])]

Modified(user) ==
    LastLogEntry(user).file /= file[user]

Write(user, line_num) ==
    /\ user \in USERS
    /\ line_num \in TEXT_LINES
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ file' = [u \in PARTICIPANTS |-> IF u = user 
                                       THEN NewFile(user, line_num)
                                       ELSE file[u]]
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)
    /\ Modified(user) = FALSE
    /\ UNCHANGED <<log>>

NewLogEntry(user) ==
    [user |-> user, file |-> file[user]]

Commit(user) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ user \in USERS
    /\ Modified(user)
    /\ Len(log[user]) < MAX_LOG_SIZE
    /\ log' = [u \in PARTICIPANTS |-> IF u = user
                                      THEN Append(log[user], NewLogEntry(user))
                                      ELSE log[u]]
    /\ UNCHANGED <<file>>
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

AbleToPush(user) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ user \in USERS
    /\ Len(log[user]) >= Len(log[SERVER])
    /\ Len(log[SERVER]) < MAX_LOG_SIZE
    /\ \A i \in DOMAIN log[SERVER]: log[SERVER][i] = log[user][i]
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

Push(user) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ AbleToPush(user)
    /\ log' = [p \in PARTICIPANTS |-> IF p = SERVER
                                      THEN log[user]
                                      ELSE log[p]]
    /\ file' = [p \in PARTICIPANTS |-> IF p = SERVER
                                       THEN LastLogEntry(user).file
                                       ELSE file[p]]
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

WriteAction ==
    \E user \in USERS, line_num \in TEXT_LINES:
        /\ Write(user, line_num)

CommitAction ==
    \E user \in USERS:
        Commit(user)

PushAction ==
    \E user \in USERS:
        Push(user)

InitFile == [l \in TEXT_LINES |-> INIT_VALUE]
\* Тут небольшое изменение: автором первой записи в логе становится сервер.
InitLog == <<[user |-> SERVER, file |-> InitFile]>>

Init ==
    /\ file = [u \in PARTICIPANTS |-> InitFile]
    /\ log = [p \in PARTICIPANTS |-> InitLog]

Next ==
    \/ WriteAction
    \/ CommitAction
    \/ PushAction

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

\* Количество записей в логе ограничено некоторой константой и не может
\* быть превышено.
LogIsBounded ==
    \A u \in PARTICIPANTS: Len(log[u]) <= MAX_LOG_SIZE

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
LogAlwaysGrows ==
    \A u \in PARTICIPANTS: <>(Len(log[u]) = MAX_LOG_SIZE)

\* Каждая запись в логе пользователя отражает изменение в одной и только одной
\* строке файла. Не должно быть ситуации, когда любые две соседние записи
\* в логе отличались больше чем на одну строку.
DiffBetweenConsequentEntries ==
    \A u \in USERS: \A i \in DOMAIN log[u]: i + 1 \in DOMAIN log[u] =>
        \E line_num \in TEXT_LINES:
            /\ log[u][i].file[line_num] /= log[u][i + 1].file[line_num]
            /\ \A other_line_num \in TEXT_LINES: other_line_num /= line_num =>
                    log[u][i].file[other_line_num] = log[u][i + 1].file[other_line_num]

(* VVVV     INSERT YOU CODE HERE     VVVV *)

\* ОПЦИОНАЛЬНОЕ место для дополнительных инвариантов.

(* ^^^^     INSERT YOU CODE HERE     ^^^^ *)
====