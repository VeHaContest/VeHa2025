----MODULE 5_server_pull----
EXTENDS Naturals, Sequences

(*    ОПИСАНИЕ СПЕЦИФИКАЦИИ №5    *)

(* В этой спецификации мы добавляем действие Pull: скачивание изменений с
   сервера, но только в случае, если нет конфликтов.

   В задании нужно сделать следующее:
   1) Перенести все нужное, что было добавлено вами в предыдущих спецификациях.
   2) Сформулировать свойство отсутствия конфликтов, которое позволит выполнять
      действие Pull. Заметьте, что конфликты в спецификации возможны, их
      разрешением мы займемся в следующей спецификации, где нужно будет
      реализовать действие Merge.
   3) Реализовать тело оператора AbleToPull и действие Pull.

   AbleToPull должен удовлетворять следующим требованиям:
   1) Проверять, что при выполнении Pull не перезапишутся никакие записи в логе
      пользователя, которые там присутствуют.
   2) Проверить, что действие Pull не нарушит никаких инвариантов.

   Pull должен удовлетворять следующим требованиям:
   1) Результат операции: лог сервера и некоторого пользователя User становятся
      одинаковы (синхронизированы) за счет скачивания изменений с сервера.
      Что значит скачивание?
   2) Не забыть про локальную копию файла. Что с ней нужно сделать и где?

   Проверить корректность спецификации запуском TLC. Если инструмент находит
   ошибку, нужно разобраться, какое из сформулированных в спецификации условий
   нарушается и как это можно исправить.

   Иначе дальше попробовать сделать следующее:
   1) Раскомментировать инвариант LogsConverge из конфигурационного файла
      (5_server_pull.cfg).
   2) Запустить TLC заново, разобраться почему происходит нарушение инварианта.
   3) Переходить к следующему заданию и исправить нарушение там.

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
    [file EXCEPT ![user][line_num] = @ * line_num * user]

LastLogEntry(user) ==
    log[user][Len(log[user])]

Modified(user) ==
    LastLogEntry(user).file /= file[user]

Write(user, line_num) ==
    /\ user \in USERS
    /\ line_num \in TEXT_LINES
    /\ Len(log[user]) < MAX_LOG_SIZE
    /\ Modified(user) = FALSE
    /\ file' = NewFile(user, line_num)
    /\ UNCHANGED <<log>>

NewLogEntry(user) ==
    [user |-> user, file |-> file[user]]

Commit(user) ==
    /\ Modified(user) = TRUE 
    /\ log' = [log EXCEPT ![user] = Append(@, NewLogEntry(user))]
    /\ UNCHANGED <<file>>

\* log1 включен в log2 (строгое включение)
Include(log1, log2) ==
    /\ Len(log2) > Len(log1)
    /\ log1 = SubSeq(log2, 1, Len(log1))

\* Отправить указанный лог (from) в назваченное место (to)
TransferLog(from, to) ==
    log' = [log EXCEPT ![to] = log[from]]

\* Отправить указанный файл (from) в назваченное место (to)
TransferFile(from, to) ==
    file' = [file EXCEPT ![to] = file[from]]

AbleToPush(user) ==
    /\ user \in USERS
    /\ Include(log[SERVER], log[user])

Push(user) ==
    /\ AbleToPush(user)
    /\ TransferLog(user, SERVER)
    /\ TransferFile(user, SERVER)

AbleToPull(user) ==
    /\ user \in USERS
    /\ Modified(user) = FALSE \* Чтобы при затягивании изменений не потерять текущее содержимое файла.
    /\ Include(log[user], log[SERVER])

Pull(user) ==
    /\ AbleToPull(user)
    /\ TransferLog(SERVER, user)
    /\ TransferFile(SERVER, user)

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
    \/ PullAction

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

\* При штатном функционировании системы (см. fairness в документации TLA+)
\* если логи всех пользователей заполнены (действие Next не может быть
\* выполнено), то логи стали одинаковы и синхронизированы.
\* Другими словами, невозможна ситуация, в которой логи разных пользователей
\* расходятся настолько, что их синхронизация через сервер становится
\* невозможна. Не работает для MAX_USERS >= 2, если в спецификации не описано
\* разрешения конфликтов.
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

(* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

====