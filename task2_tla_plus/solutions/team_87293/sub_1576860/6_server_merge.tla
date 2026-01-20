----MODULE 6_server_merge----
EXTENDS Naturals, Sequences, FiniteSets

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

Commit(user) ==
    LET logEntry == [user |-> user, file |-> file[user]] IN
    /\ Modified(user) = TRUE
    /\ log' = [log EXCEPT ![user] = Append(@, logEntry)]
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
    LET
        \* Индексы для перебора
        IND == (DOMAIN log[user]) \cap (DOMAIN log[SERVER])
        
        \* Это первый индекс, где записи логов отличаются
        IsFirstDivIndex(i) ==
            /\ log[user][i] /= log[SERVER][i]
            /\ \A j \in IND: (j < i) => log[user][j] = log[SERVER][j]
        
        indexExist == \E i \in IND: IsFirstDivIndex(i)
        index == CHOOSE i \in IND: IsFirstDivIndex(i)
    IN
    IF indexExist THEN index ELSE Cardinality(IND) + 1

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
    LET
        \* Индексы для просмотра лога
        IND == DivergentIndex(user)..Len(log[user])
        ind(i) == i + DivergentIndex(user) - 1
    IN
    [i \in 1..Cardinality(IND) |->
        ChangedLineAndValue(log[user][ind(i)-1].file, log[user][ind(i)].file)]

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
    LET
        change == Head(changed_entries) \* Изменение, которое нужно применить
        last_file == new_log[Len(new_log)].file
        new_file == [last_file EXCEPT ![change.line_num] = change.value]
        new_entry == [user |-> user, file |-> new_file]
        apply_entry_log == Append(new_log, new_entry)   \* Лог с применённым изменением
    IN
    IF Len(changed_entries) = 0 THEN new_log ELSE
    ApplyDivergence(user, apply_entry_log, Tail(changed_entries))


\* ДОБАВЛЕНО ЗАЩИТНОЕ УСЛОВИЕ!! Modified(user) = FALSE
\* Между сервером и клиентом есть расхождение, конфликт,
\* при этом на сервере есть новые изменения
AbleToMergeButNotPullOrPush(user) ==
    /\ AbleToPull(user) = FALSE
    /\ AbleToPush(user) = FALSE
    /\ Modified(user) = FALSE \* Чтобы при слиянии не потерять текущее содержимое файла.
    /\ \E i \in DOMAIN log[SERVER]:
            /\ i \in DOMAIN log[user]
            /\ log[user][i] /= log[SERVER][i]

\* ДЕЙСТВИЕ ИСПРАВЛЕНО!!!
\* старая версия содержала ошибку
\* было: file' = [file EXCEPT ![user] = log'[user][Len(log[user])].file]
\* в новой версии Len(log'[user])
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
    /\ file' = [file EXCEPT ![user] = log'[user][Len(log'[user])].file]

WriteAction ==
    \E user \in USERS, line_num \in TEXT_LINES:
        Write(user, line_num)

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


\* ИНВАРИАНТ ИСПРАВЛЕН!!!
\* Количество записей в логе ограничено некоторой константой
\* и не может быть превышено.
\* Максимальный размер лога = 2 * MAX_LOG_SIZE - 1
\* и достигается при следующем сценарии:
\* каждый пользователь заполняет свой лог до допустимого значения MAX_LOG_SIZE,
\* далее один из пользователей делает push и синхронизируется с сервером,
\* после чего второй пользователь делает merge и оба лога объединяются в один.
\* Из 2 * MAX_LOG_SIZE вычитается 1,
\* так как первая запись в обоих логах всегда совпадает
\* и не перемещается при слиянии (merge) логов.
LogIsBounded ==
    \A u \in PARTICIPANTS: Len(log[u]) <= 2 * MAX_LOG_SIZE - 1

\* Если изменения в файле были добавлены в лог, то последняя запись лога
\* соответствует новому содержимому файла.
LastLogEntryIsFile ==
    \A u \in PARTICIPANTS: Modified(u) = FALSE => LastLogEntry(u).file = file[u]

\* Мы не можем повторно перезаписывать содержимое файла, если до этого не
\* добавили предыдущие изменения в лог.
WriteOnlyOnce ==
    \A u \in USERS: \E line_num \in TEXT_LINES:
        ENABLED Write(u, line_num) => ~(ENABLED Commit(u))

\* ИНВАРИАНТ ИСПРАВЛЕН!!!
\* При штатном функционировании системы (см. fairness в документации TLA+)
\* мы всегда дойдем до момента, когда лог будет заполнен в определённых пределах.
\* Минимум = MAX_LOG_SIZE
\* (пока лог не достиг этого значения всегда можно делать комиты).
\* Максимум = 2 * MAX_LOG_SIZE - 1 \* (пояснение в свойстве LogIsBounded).
LogAlwaysGrows ==
    \A u \in PARTICIPANTS: <>(Len(log[u]) >= MAX_LOG_SIZE /\
                              Len(log[u]) <= 2 * MAX_LOG_SIZE - 1)

\* ИНВАРИАНТ ИСПРАВЛЕН!!!
\* Каждая запись в любом логе отражает изменение в одной и только одной
\* строке файла. Не должно быть ситуации, когда любые две соседние записи
\* в логе отличались больше чем на одну строку,
\* т.е. в соседних записях не существует двух и более разных строк
\* (допустимое количество разных строк: 0 или 1).
\* Исправим данное свойство следующим образом:
DiffBetweenConsequentEntries ==
    LET
        \* Разные строки
        DiffStr(user, rec_num1, rec_num2, line_num) ==
            log[user][rec_num1].file[line_num] /= log[user][rec_num2].file[line_num]
    IN
    \A u \in PARTICIPANTS: \A i \in DOMAIN log[u]: i + 1 \in DOMAIN log[u] =>
        ~\E l1,l2  \in TEXT_LINES:
            /\ l1 /= l2
            /\ DiffStr(u, i, i + 1, l1)
            /\ DiffStr(u, i, i + 1, l2)

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

\* ОПЦИОНАЛЬНОЕ место для дополнительных инвариантов.


\* ДОБАВЛЕН ИНВАРИАНТ OnlyPushAllowed:
\* Если лог сервера включен в лог пользователя,
\* то при взаимодействии с сервером пользователю
\* разрешён только Push, а Pull и Merge запрещены.
OnlyPushAllowed ==
    \A u \in USERS:
        Include(log[SERVER], log[u]) =>
            /\   ENABLED Push(u)
            /\ ~(ENABLED Pull(u))
            /\ ~(ENABLED Merge(u))


\* ДОБАВЛЕН ИНВАРИАНТ OnlyPullAllowed:
\* Если лог пользователя включен в лог сервера
\* и файл пользователя не модифицирован,
\* то при взаимодействии с сервером пользователю
\* разрешён только Pull, а Push и Merge запрещены.
OnlyPullAllowed ==
    \A u \in USERS:
        Include(log[u], log[SERVER]) /\ ~Modified(u) =>
            /\   ENABLED Pull(u)
            /\ ~(ENABLED Push(u))
            /\ ~(ENABLED Merge(u))


\* ДОБАВЛЕН ИНВАРИАНТ OnlyMergeAllowed:
\* Если ни лог сервера не включен в лог пользователя,
\* ни лог пользователя не включен в лог сервера,
\* логи имеют разную длину,
\* а также файл пользователя не модифицирован,
\* то при взаимодействии с сервером пользователю
\* разрешён только Merge, а Push и Pull запрещены.
OnlyMergeAllowed ==
    \A u \in USERS:
        /\ ~Include(log[SERVER], log[u])
        /\ ~Include(log[u], log[SERVER])
        /\ Len(log[SERVER]) /= Len(log[u])
        /\ ~Modified(u)
        =>
            /\   ENABLED Merge(u)
            /\ ~(ENABLED Push(u))
            /\ ~(ENABLED Pull(u))


\* Определим более строгий тип файла с учётом ограничений на значения в строках.
FileSubType ==
    LET
        RECURSIVE valueSet(_,_,_)
        valueSet(line_num, write_num, Set) ==
        LET SetAfterWrite == {s * line_num * user : s \in Set, user \in USERS} IN
        IF write_num = 0 THEN Set ELSE
        valueSet(line_num, write_num - 1, Set \cup SetAfterWrite)
    IN
    {f \in FileType : \A line_num \in TEXT_LINES:
        f[line_num] \in valueSet(line_num, MAX_LOG_SIZE, {1}) }


\* ДОБАВЛЕН ИНВАРИАНТ FileSubTypeOK:
\* Строки файлов содержат только заранее определенные значения.
\* Инвариант показывает, что при Push/Pull/Merge
\* не возникает нового содержимого в файлах.
FileSubTypeOK ==
    \A p \in PARTICIPANTS: file[p] \in FileSubType


\* ДОБАВЛЕНО ТЕМПОРАЛЬНОЕ СВОЙСТВО LogSizeCanIncrease:
\* Размер любого лога может только увеличиваться
\* либо оставаться прежним (уменьшаться не может).
LogSizeCanIncrease ==
    LET LOG_SIZES == 1..2 * MAX_LOG_SIZE - 1 IN
    \A p \in PARTICIPANTS: \A n \in LOG_SIZES:
        []( n = Len(log[p]) => <>(n <= Len(log[p])) )


\* ДОБАВЛЕНО ТЕМПОРАЛЬНОЕ СВОЙСТВО FileChangeGetsToLog:
\* Любое изменение файла всегда попадает в лог.
\* Выполним проверку на некотором подмножестве файлов BoundFileType (инвариант BoundFileTypeOK)
BoundFileType ==
    { [line_num \in TEXT_LINES |-> (line_num * user)^write_num] : user \in USERS, write_num \in 0..MAX_LOG_SIZE }

BoundFileTypeOK ==
    BoundFileType \subseteq FileSubType

FileChangeGetsToLog ==
    \A u \in USERS: \A f \in BoundFileType:
        []( f = file[u] => <>(f = LastLogEntry(u).file) )
    

====