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

NewFile(user, line_num) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    (* [file EXCEPT ![user][line_num] = file[user][line_num] * line_num * user] 
        Для прохождения теста Success из файла 2_users.tla *)
    [file EXCEPT ![user][line_num] = file[user][line_num] * line_num * (user + 2)]
    (* Если я правильно понимаю,
       функция (f |-> f * line_num * user) была выбрана для того,
       чтобы все коммиты пользователей были уникальны (?).
       Однако это не так,
       ведь пользователи 1 и 2 могут получить одинаковый файл разными путями:
       <<1, 1, 1>> -> <<1, 2, 1>> -> <<1, 4, 1>>;
       <<1, 1, 1>> -> <<1, 4, 1>>.

       Почему это плохо?
       Допустим мы хотим сделать Merge этих двух логов.
       Первый индекс расхождения -- 2, поэтому после Merge лог будет таким:
       <<1, 1, 1>> -> <<1, 2, 1>> -> <<1, 4, 1>> -> <<1, 4, 1>>,
       где последний коммит меняет автора с 1 на 2.
       Таким образом, нужно думать, что делать в ситуации,
       когда разные пользователи имеют одинаковые коммиты.
       Предложенная схема решения с использованием оператора ChangedEntries
       не учитывает эту ситуации.
       Инвариант DiffBetweenConsequentEntries запрещает коммиты не изменяющие тело файла.
       
       Предлагаю просто изменить тело оператора NewFile так,
       чтобы коммиты стали уникальными.
       Поскольку числа 3, 4, 5 = 1 + 2, 2 + 2, 3 + 2 попарно взаимно просты,
       домножение на них делают коммиты пользователей уникальными.
       
       Добавим также проверку того,
       что все коммиты уникальны ниже
       в разделе для собственных инвариантов. *)
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

LastLogEntry(user) ==
    log[user][Len(log[user])]

Modified(user) ==
    LastLogEntry(user).file /= file[user]

Write(user, line_num) ==
    /\ user \in USERS
    /\ line_num \in TEXT_LINES
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ file' = NewFile(user, line_num)
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)
    /\ Modified(user) = FALSE
    /\ UNCHANGED <<log>>

NewLogEntry(user) ==
    [user |-> user, file |-> file[user]]

Commit(user) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ user \in USERS
    /\ Modified(user) = TRUE
    /\ Len(log[user]) < MAX_LOG_SIZE
    /\ log' = [ log EXCEPT ![user]= Append(log[user], [user |-> user, file |-> file[user]])]
    /\ UNCHANGED <<file>>
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

AbleToPush(user) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ Len(log[SERVER]) < Len(log[user])
    /\ SubSeq(log[user], 1, Len(log[SERVER])) = log[SERVER]
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

Push(user) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ user \in USERS
    /\ AbleToPush(user) = TRUE
    /\ log' = [log EXCEPT ![SERVER] = log[user]]
    /\ file' = [file EXCEPT ![SERVER] = LastLogEntry(user).file]
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

AbleToPull(user) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ Len(log[user]) < Len(log[SERVER])
    /\ SubSeq(log[SERVER], 1, Len(log[user])) = log[user]
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

Pull(user) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    /\ user \in USERS
    /\ AbleToPull(user) = TRUE
    /\ log' = [log EXCEPT ![user] = log[SERVER]]
    /\ file' = [file EXCEPT ![user] = LastLogEntry(SERVER).file]
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
    LET D == {j \in DOMAIN log[user] : j \in DOMAIN log[SERVER] /\ log[user][j] /= log[SERVER][j]} IN
        IF D /= {}
        THEN CHOOSE i \in D : \A j \in D : i <= j
        ELSE Len(log[user])
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
    LET i == DivergentIndex(user) IN
        [j \in 1..(Len(log[user]) - i + 1) |-> ChangedLineAndValue(log[user][i + j - 2].file, log[user][i + j - 1].file)]
    (* ^^^^     INSERT YOU CODE HERE     ^^^^ *)

(* Данная операция берет в качестве базы некоторый лог new_log,
   последовательность всех модификаций файла, которые конфликтуют с записями
   сервера (получено с помощью оператора ChangedEntries для некоторого
   пользователя) и пользователя user, и рекурсивно конструирует новый лог,
   итеративно добавляя в конец new_log новую запись, полученную путем
   применения изменений из головы последовательности changed_entries.
   Если changed_entries пуст, то возвращается итоговое значение new_log.

Если changed_entries = <<
    [line_num |-> 2, value |-> 3],
    [line_num |-> 3, value |-> 5]
    >>

и log[SERVER] = <<
    [file |-> <<1, 1, 1>>, user |-> 0]
    [file |-> <<2, 1, 1>>, user |-> 1]
    [file |-> <<2, 1, 4>>, user |-> 2]
    [file |-> <<2, 5, 4>>, user |-> 2]>>

То ApplyDivergence(1, new_log, changed_entries) = <<
    [file |-> <<1, 1, 1>>, user |-> 0]
    [file |-> <<2, 1, 1>>, user |-> 1]
    [file |-> <<2, 1, 4>>, user |-> 2]
    [file |-> <<2, 5, 4>>, user |-> 2]
    [file |-> <<2, 3, 4>>, user |-> 1]
    [file |-> <<2, 3, 5>>, user |-> 1]
    >>
*)
RECURSIVE ApplyDivergence(_, _, _)
ApplyDivergence(user, new_log, changed_entries) ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    IF changed_entries = <<>> THEN new_log
    ELSE
        LET c == Head(changed_entries) IN
        LET new_file == [new_log[Len(new_log)].file EXCEPT ![c.line_num] = c.value] IN
        LET newer_log == Append(new_log, [user |-> user, file |-> new_file]) IN
        ApplyDivergence(user, newer_log, Tail(changed_entries))
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
    /\ file' = [file EXCEPT ![user] = log'[user][Len(log[user])].file]

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

\* Количество записей в логе ограничено некоторой константой и не может
\* быть превышено. ИСПРАВЬТЕ ЭТОТ ИНВАРИАНТ.
LogIsBounded ==
    (* VVVV     INSERT YOU CODE HERE     VVVV *)
    \A u \in PARTICIPANTS: Len(log[u]) <= MAX_LOG_SIZE * 2 - 1
    (* При Merge у нас может быть (MAX_LOG_SIZE - 1) собственных локальных коммитов
        и ещё MAX_LOG_SIZE коммитов на сервере *)
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
    \A u \in PARTICIPANTS: <>(Len(log[u]) >= MAX_LOG_SIZE)
    (* Логи стабилизируются, это гарантирует свойство LogsConverge,
       однако размер итогового лога может быть любым
       от MAX_LOG_SIZE до MAX_LOG_SIZE * 2 - 1
       взависимости от размера Merge. *)
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
(* Если два коммита имеют одинаковое тело,
   то их авторы совпадают. *)
UniqueCommits ==
    \A u1 \in PARTICIPANTS, u2 \in PARTICIPANTS:
        \A i \in DOMAIN log[u1]: \A j \in DOMAIN log[u2]:
        log[u1][i].file = log[u2][j].file =>
        log[u1][i].user = log[u2][j].user
(* ^^^^     INSERT YOU CODE HERE     ^^^^ *)
====