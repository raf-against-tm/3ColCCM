;SOLUCION PARA EL PROBLEMA 3-COL MEDIANTE COMPUTACION CELULAR CON MEMBRANAS.

;RAFAEL VALLE MORALES. INGENIERIA INFORMATICA (PLAN 97)

;[ARCHIVO SIN TILDES]

;El problema 3-COL consiste en determinar si un mapa puede ser coloreado unicamente con 3 colores, teniendo
; en cuenta que las regiones contiguas deben tener colores distintos. Toda instancia del problema es codificada
; por un grafo cuyos vertices determinan las distintas regiones del mapa, y cuyas aristas definen las fronteras entre
; dichas regiones. De manera que, los datos de entrada del sistema seran los elementos (vertices y aristas) del grafo
; correspondiente al mapa sobre el que se desea obtener una respuesta.


;BIBLIOGRAFIA (REFERENCIAS Y DOCUMENTACION)

;R1.Every planar graph is four colorable - Part1: Discharging
;   [https://projecteuclid.org/euclid.ijm/1256049011]
;R2.Every planar graph is four colorable - Part2: Reducibility
;   [https://projecteuclid.org/euclid.ijm/1256049012]
;R3.Solving 3-COL with Tissue P Systems
;   [http://www.gcn.us.es/4BWMC/vol2/diaz.pdf]
;R4.A uniform family of tP systems with cell division solving 3-COL in a linear time
;   [http://www.sciencedirect.com/science/article/pii/S030439750800251X]

;D1.CLIPS Documentation
;   [http://www.clipsrules.net/?q=Documentation]
;D2.CLIPS Basic Reference Guide
;   [https://www.csie.ntu.edu.tw/~sylee/courses/clips/bpg/top.html]
;D3.Conceptos basicos de la computacion celular con membranas
;   [http://www.sema.org.es/ojs/index.php?journal=sema&page=article&op=view&path%5B%5D=191]
;D4.Modelos de computacion celular con membranas
;   [http://www.p-lingua.org/mecosim/matvida/course/Unidad2_Computaci%F3nCelularConMembranas.pdf]
;D5.A CLIPS simulator for Recognizer P Systems with Active Membranes
;   [http://cantor.cs.us.es/2BWMC/bravolpdf/CLIPS.pdf]

;BREVE EXPLICACION DE LA IMPLEMENTACION LLEVADA A CABO.

;La aplicacion incluye una interfaz de usuario de manera que, al cargar el fichero, permite seleccionar una serie
; de opciones para la ejecucion de la misma. Las opciones disponibles son, lanzar el proceso de resolucion para un ejemplo
; concreto (se proporcionan dos ejemplos), y lanzar el proceso de resolucion para un ejemplo especificado manualmente. Si se
; especifica el ejemplo manualmente, este debe ser introducido segun la sintaxis especificada en su momento.
;
;Por otra parte, se han incluido una serie de reglas para imprimir por pantalla los datos de las distintas configuraciones por las
; que pasa el sistema en la resolucion del problema. Tambien se imprimen las reglas aplicadas a cada configuracion para llegar a la
; siguiente.
;
;El resto de la implementacion se basa en el modelo de computacion celular a modo tejido con membranas activas. En primer lugar,
; se lleva a cabo una inicializacion que permite obtener el sistema P concreto que servira para obtener una solucion al problema.
; Dicha inicializacion se realiza a partir de los datos de entrada que codifican la instancia del problema a resolver.
;
;Tras la inicializacion, comienza la computacion. Se han implementado varias reglas auxiliares para llevar a cabo las acciones necesarias
; para el paso de una configuracion a otra y en definitiva determinar cuando termina un paso de la computacion y comienza uno nuevo,
; asi como, para determinar el final de la computacion debido a la llegada del sistema a una configuracion de parada. En cada paso
; de la computacion se podran aplicar dos tipos de reglas de acuerdo al modelo computacional, de division y de comunicacion. La aplicacion
; de dichas regla deben cumplir una serie de restricciones indicadas mas adelante.
;
;Para simplificar, en la medida de lo posible, la implementacion de las reglas de division y comunicacion se han usado varias
; funciones auxiliares con objeto de abstraer a la propia regla de los procesos de manipulacion de las estructuras de datos. Dichas
; funciones cubren operaciones como las de inlcuir/eliminar elementos del contenido de una membrana, asi como la de comprobar si
; existe un elemento en el contenido de las mismas.

;ESTRUCTURAS DE DATOS

; Los elementos que forman parte del alfabeto de trabajo del sistema se denotan de la siguente forma: SIMBOLO INDICE-i INDICE-j
;  Un elemento puede tener uno, dos indices o ninguno y cuando se trata del contenido de una membrana deben incluir el numero
;  de copias del mismo. Excepcionalmente, el contenido de la membrana etiquetada con 0 (modela al entorno), no indica el numero de copias
;  de cada elemento porque se supone que siempre tendra el numero de copias necesarias de cada uno de los que contiene. Por tanto, para
;  simplificar y ganar algo de eficiencia en el proceso, su contenido permanece inalterado hasta que se incluya uno de los elementos
;  de respuesta como solucion del problema.
;
; Ademas, cada elemento debe separarse mediante comas, incluyendo una coma inicial y una final para delimitar la lista de los mismos.
;  De esta manera en el contenido de una membrana que no sea el entorno tendrian la forma siguiente:
;  , ... , COPIAS SIMBOLO INDICE-i INDICE-j , ... ,
;  Y en el contenido de la membrana que modela al entorno seria de la forma:
;  , ... , SIMBOLO INDICE-i INDICE-j , ... ,
;
; El uso de la coma como separador sirve para que en la equiparacion de patrones de CLIPS puedan seleccionarse los elementos
;  correctamente y no haya posibles activaciones con subcadenas que no referencian a un elemento concreto.
;
; Con respecto a la inclusion de un contador de copias, se llego a la conclusion de que era la mejor opcion tras probar
;  con la opcion de generar tantos elementos como copias eran necesarias de cada uno, pues el proceso se hacía tremendamente costoso
;  para la equiparacion de patrones de CLIPS. Ademas, si teniamos 4 elementos , C 3 , C 3 , C 3 , C 3 , y una regla que afectara a C 3,
;  se producian muchas activaciones innecesarias para la misma regla en un paso, a pesar de que solo se llegue a disparar una.

(deftemplate membrana "datos que definen una membrana dentro del sistema p"

  (slot etiqueta
    (type INTEGER))
  (slot identificador   ;La etiqueta de una membrana es insifuciente para identificar cada membrana, pues puede haber
    (type INTEGER))     ; multiples membranas con una misma etiqueta.
  (slot configuracion
    (type INTEGER)
    (default 1))
  (multislot contenido) ; , ... , [COPIAS] SIMBOLO [INDICE-i] [INDICE-j] , ... ,

)

;Es necesario la definicion de estructuras de datos para las reglas del sistema P concreto, pues estas dependen de los
; datos de entrada del mismo. Solo hay dos tipos de reglas, pero cada tipo de regla puede tener multiples instancias que realizan
; acciones diferentes o afectan a elementos distintos.
;
;En los casos de las reglas cada elemento se especifica como SIMBOLO INDICE-i INDICE-j, al indicar un unico elemento
; no es necesario incluir comas.

(deftemplate regla-division "datos que definen una regla de division para el sistema p"

  ;[elemento-izquierda](etiqueta) -> [elemento1-derecha](etiqueta)[elemento2-derecha](etiqueta)

  (slot etiqueta
    (type INTEGER))
  (multislot elemento-izquierda)
  (multislot elemento1-derecha)
  (multislot elemento2-derecha)

)

(deftemplate regla-comunicacion "datos que definen una regla de comunicacion para el sistema p"

  ;(etiqueta-izquierda, elemento1-izquierda elemento2-izquierda/elemento1-derecha elemento2-derecha, etiqueta-derecha)

  ;Una regla de comunicacion tiene como maximo 4 elementos, 2 maximo por parte de la membrana con etiqueta-izquierda
  ; y otros 2 maximo por parte de la membrana con etiqueta-derecha. Los elementos especificados de cada membrana seran
  ; los intercambiados entre las mismas.

  (slot etiqueta-izquierda
    (type INTEGER))
  (multislot elemento1-izquierda)
  (multislot elemento2-izquierda)
  (slot etiqueta-derecha
    (type INTEGER))
  (multislot elemento1-derecha)
  (multislot elemento2-derecha)

)

;Los datos referentes a una instancia del problema son agrupados en una estructura de datos por comodidad y para activar
; la inicializacion del sistema. Aqui al igual que en las membranas se hace uso del mismo formato para determinar
; los elementos referentes a los vertices y las aristas, salvo por la no inclusion del numero de copias que no es necesario en
; este caso.

(deftemplate instancia-3col "datos que definen una instancia del problema 3-COL a partir del grafo que la codifica"

  (slot n-vertices
    (type INTEGER))
  (multislot vertices) ;(vertices , A 1 , A 2 , ... , An ,)
  (slot m-aristas
    (type INTEGER))
  (multislot aristas)  ;(aristas , A 1 2 , A 1 3 , ... , A i j ,) con 1 <= i < j <= n

)

;VARIABLES GLOBALES
(defglobal ?*n-vertices*   = 0  ;Numero de vertices que codifican las distintas regiones del mapa.
           ?*m-aristas*    = 0  ;Numero de aristas que codifican las fronteras entre regiones del mapa.
           ?*techo-log2-m* = 0  ;Valor necesario para la generacion de ciertos elementos en funcion de la instancia del problema.
           ?*id*           = 2) ;Valor de referencia para identificar nuevas membranas producto de la division celular.

;FUNCIONES AUXILIARES
(deffunction techo (?valor) "calcula la funcion matematica techo del valor pasado como parametro"
  (if (> ?valor (integer ?valor)) then (+ (integer ?valor) 1) else (integer ?valor))

)

(deffunction agrega-elementos (?contenido ?k $?elemento) "agrega k copias del elemento dado al contenido especificado"

  ;Si hay algun elemento identico en el contenido los agrupa y si no, lo incluye en el mismo.

  (if (= (length$ $?elemento) 0) ;Se trata de un elemento vacio.
    then (return ?contenido))

  (bind ?posiciones (member$ (create$ $?elemento ,) ?contenido))

  (if (neq ?posiciones FALSE)
    then (bind ?pos1    (- (nth$ 1 ?posiciones) 1))
         (bind ?pos2    (- (nth$ 2 ?posiciones) 1))

         (bind ?copias  (nth$ ?pos1 ?contenido))

         (replace$ ?contenido ?pos1 ?pos2 (create$ (+ ?k ?copias) $?elemento))

    else (insert$ ?contenido 1 , ?k $?elemento))

)

(deffunction elimina-elementos (?contenido ?k $?elemento) "elimina k copias del elemento dado en el contenido especificado"

  ;Si el elemento a eliminar no existe o no hay suficientes en el contenido devuelve FALSE

  (if (= (length$ $?elemento) 0) ;Se trata de un elemento vacio.
    then (return ?contenido))

  (bind ?posiciones (member$ (create$ $?elemento ,) ?contenido))

  (if (neq ?posiciones FALSE)
    then (bind ?pos1    (- (nth$ 1 ?posiciones) 1))
         (bind ?pos2    (- (nth$ 2 ?posiciones) 1))

         (bind ?copias  (nth$ ?pos1 ?contenido))
         (bind ?restantes (- ?copias ?k))

         (if (= ?restantes 0)
           then (return (delete$ ?contenido (- ?pos1 1) ?pos2))) ;Elimina completamente el elemento.

         (if (> ?restantes 0)
           then (return (replace$ ?contenido ?pos1 ?pos1 ?restantes))))

)

(deffunction existe-elemento (?contenido ?k $?elemento) "comprueba si existen k copias del elemento dado en el contenido especificado"

  ;Si el elemento existe y hay copias suficientes devuelve TRUE.

  (if (= (length$ $?elemento) 0) ;Se trata de un elemento vacio.
    then (return TRUE))

  (bind ?posiciones (member$ (create$ $?elemento ,) ?contenido))

  (if (neq ?posiciones FALSE)
    then (bind ?pos1    (- (nth$ 1 ?posiciones) 1))
         (bind ?pos2    (- (nth$ 2 ?posiciones) 1))

         (bind ?copias  (nth$ ?pos1 ?contenido))
         (bind ?restantes (- ?copias ?k))

         (return (>= ?restantes 0)))

)

;REGLAS (INTERFAZ DE USUARIO, INICIALIZACION, CONTROL DE LA COMPUTACION, DIVISION y COMUNICACION)

;INTERFAZ DE USUARIO
(defrule seleccion-de-opciones "permite al usuario seleccionar que entrada desea para el proceso"

  ?inicio <- (initial-fact)

  =>
  (retract ?inicio)

  (printout t "--> ////////// SOLUCION PARA EL PROBLEMA 3-COL MEDIANTE COMPUTACION CELULAR A MODO TEJIDO //////////  " crlf crlf)

  (printout t "--> Por favor indique una de las siguientes opciones introduciendo el valor correspondiente:" crlf crlf)
  (printout t "    1: Ejemplo 1 - Mapa con 3 regiones contiguas entre si" crlf)
  (printout t "       [Representado por un grafo de vertices A1, A2 y A3 con aristas A12, A13 y A23]" crlf crlf)
  (printout t "    2: Ejemplo 2 - Mapa con 4 regiones contiguas entre si" crlf)
  (printout t "       [Representado por un grafo de vertices A1, A2, A3 y A4 con aristas A12, A13, A14, A23, A24 y A34]" crlf crlf)
  (printout t "    3: Ej.Manual - Introduce manualmente un ejemplo para resolverlo" crlf)
  (printout t "       [Los datos introducidos se deben corresponder con el grafo que representa el problema]" crlf crlf)

  (printout t "--> Indique la opcion escogida [1, 2 o 3]: ")
  (bind ?opcion (read))

  ;Validacion de la opcion escogida.
  (while (and (neq ?opcion 1) (neq ?opcion 2) (neq ?opcion 3))
    (printout t "--> Ha introducido un valor incorrecto, por favor vuelva a indicar la opcion [1, 2 o 3]: ")
    (bind ?opcion (read)))

  (printout t crlf)

  ;Ejecucion de la opcion escogida.
  (switch ?opcion

    ;Ejemplo1: Existe solucion 3-COL.
    (case 1 then
      (assert (estado inicializacion)
              (paso-actual 1)
              (paso-siguiente 2)

              (instancia-3col (n-vertices 3) (vertices , A 1 , A 2 , A 3 ,)
                              (m-aristas 3) (aristas , A 1 2 , A 1 3 , A 2 3 ,))))

    ;Ejemplo2: No existe solucion 3-COL.
    (case 2 then
      (assert (estado inicializacion)
              (paso-actual 1)
              (paso-siguiente 2)

              (instancia-3col (n-vertices 4) (vertices , A 1 , A 2 , A 3 , A 4 ,)
                              (m-aristas 6) (aristas , A 1 2 , A 1 3 , A 1 4 , A 2 3 , A 2 4 , A 3 4 ,))))

    (case 3 then (assert (lee-numero-vertices-y-aristas))))


)

;Gestion de los datos a introducir por parte del usuario, si se ha escogido la opcion manual.
(defrule lee-numero-vertices-y-aristas "se encarga de leer y validar los datos de entrada referentes al numero de vertices y aristas"

  ?lnva <- (lee-numero-vertices-y-aristas)

  =>
  (retract ?lnva)

  ;Vertices

  ;Lectura
  (printout t "--> Introduzca el numero de vertices: ")
  (bind ?n-vertices (read))

  ;Validacion
  (while (or (not (numberp ?n-vertices)) (<= ?n-vertices 0))
    (printout t "--> Debe introducir un numero valido: ")
      (bind ?n-vertices (read)))

  ;Aristas

  ;Lectura
  (printout t "--> Introduzca el numero de aristas: ")
  (bind ?m-aristas (read))

  ;Validacion
  (while (or (not (numberp ?m-aristas)) (<= ?m-aristas 0))
    (printout t "--> Debe introducir un numero valido: ")
      (bind ?m-aristas (read)))

  ;Resultado
  (assert (numero-vertices ?n-vertices)
          (numero-aristas ?m-aristas)
          (construye-lista-vertices)
          (lee-aristas ?m-aristas))

)

(defrule construye-lista-vertices "crea la lista de vertices existentes a partir del numero de vertices introducido"

  ?clc <- (construye-lista-vertices)

  (numero-vertices ?n-vertices)

  =>
  (retract ?clc)

  ;Construye el conjunto de vertices
  (bind ?i 1)
  (bind ?vertices (create$ ,))
  (while (<= ?i ?n-vertices)
    (bind ?vertices (insert$ ?vertices 1 , A ?i))
    (bind ?i (+ ?i 1)))

  (assert (vertices-validos ?vertices))

)

(defrule lee-aristas "se encarga de leer la lista de aristas de entrada indicadas por el usuario y valida su estructura"

  ?la <- (lee-aristas ?m-aristas)

  =>
  (retract ?la)

  ;Aristas
  (printout t crlf)
  (printout t "--> A continuacion debe introducir las aristas siguiendo el formato especificado en el ejemplo:" crlf crlf)
  (printout t "     [  Ejemplo: , A 1 2 , A 1 3 , A 2 3 , A 3 4 ,                                                ]" crlf)
  (printout t "     [- Cada elemento en el ejemplo debe separarse por un espacio.                                ]" crlf)
  (printout t "     [- Las aristas son determinadas por el simbolo A y sus indices denotan los vertices que unen.]" crlf)
  (printout t "     [- Los indices i j deben cumplir la condicion 1 <= i < j <= numero de vertices.              ]" crlf)
  (printout t "     [- Las comas deben incluirse, pues se usan a modo separador de cada arista.                  ]" crlf crlf)

  (printout t "--> Introduzca las aristas del grafo siguiendo las instrucciones anteriores: ")
  (bind ?aristas (explode$ (readline)))

  (bind ?longitud (length ?aristas))
  (while (< ?longitud 5)
    (printout t "--> Debe introducir al menos una arista segun las instrucciones anteriores: ")
    (bind ?aristas (explode$ (readline)))
    (bind ?longitud (length ?aristas)))

  (printout t crlf)

  ;Valida la estructura de la lista de aristas (, ... , A i j , ... ,)
  (bind ?validas TRUE)
  (bind ?i 1)
  (bind ?m-aristas-leidas 0)
  (while (< ?i ?longitud)
    (if (neq (nth$ ?i ?aristas) ,)
      then (bind ?validas FALSE))

    (if (not (symbolp (nth$ (+ ?i 1) ?aristas))) ;A
      then (bind ?validas FALSE)
           (break))

    (if (not (numberp (nth$ (+ ?i 2) ?aristas))) ;i
      then (bind ?validas FALSE)
           (break))

    (if (not (numberp (nth$ (+ ?i 3) ?aristas))) ;j
      then (bind ?validas FALSE)
           (break))

    (bind ?m-aristas-leidas (+ ?m-aristas-leidas 1))
    (bind ?i (+ ?i 4)))

  (if (neq (nth$ ?longitud ?aristas) ,)
    then (bind ?validas FALSE))

  (if ?validas
    then (assert (aristas-leidas ?m-aristas-leidas ?aristas)
                 (aristas-validas 0 ,))

    else (assert (lee-aristas ?m-aristas))
         (printout t "--> La aristas introducidas no cumplen con la estructura del ejemplo." crlf))

)

(defrule valida-aristas-leidas "comprueba cada arista de la lista introducida es correcta"

  ?al <- (aristas-leidas ?pendientes $?ai , ?s ?i ?j , $?af)
  ?av <- (aristas-validas ?validadas $?avs)

  (numero-vertices ?n-vertices)
  (numero-aristas ?m-aristas)

  =>
  (retract ?al ?av)

  (bind ?valida TRUE)

  ;Validacion para la condicion 1 <= i < j <= numero de vertices.
  (if (or (<= ?i 0) (>= ?i ?j) (>= ?i ?n-vertices))
    then (printout t "--> No se cumple la condicion 1 <= i < j <= numero de vertices para " ?s " " ?i " " ?j "." crlf)
         (bind ?valida FALSE))

  ;Validacion del simbolo que denota a una arista.
  (if (neq ?s A)
    then (printout t "--> El simbolo de la arista " ?s " " ?i " " ?j " no es correcto." crlf)
         (bind ?valida FALSE))

  ;Validacion de aristas repetidas.
  (if (member$ (create$ ?s ?i ?j) $?avs)
    then (printout t "--> La arista " ?s " " ?i " " ?j " ha sido introducida mas de una vez." crlf)
         (bind ?valida FALSE))

  ;Validacion del numero de aristas.
  (if (= ?pendientes 1)
    then (if (<> (+ ?validadas 1) ?m-aristas)
           then (printout t "--> El numero de aristas indicado no coincide con el numero de aristas introducidas." crlf)
                (bind ?valida FALSE)))

  (if ?valida
    then (assert (aristas-leidas (- ?pendientes 1) $?ai , $?af)
                 (aristas-validas (+ ?validadas 1) $?avs ?s ?i ?j ,))

    else (assert (lee-aristas ?m-aristas)))

)

(defrule construye-instancia-3-col "genera la estructura completa que necesita el sistema para comenzar"

  ?nv <- (numero-vertices ?n-vertices)
  ?ma <- (numero-aristas ?m-aristas)
  ?al <- (aristas-leidas 0 ,)
  ?av <- (aristas-validas ?m-aristas $?avs)
  ?vv <- (vertices-validos $?vvs)

  =>
  (retract ?nv ?ma ?al ?av ?vv)

  (assert (estado inicializacion)
          (paso-actual 1)
          (paso-siguiente 2))

  (assert (instancia-3col (n-vertices ?n-vertices) (vertices $?vvs)
                          (m-aristas ?m-aristas) (aristas $?avs)))

)

;INICIALIZACION
(defrule inicializa-sistema "a partir de los datos de entrada genera los hechos necesarios para inicializar el sistema"

  ?entrada <- (instancia-3col (n-vertices ?n-vertices) (vertices $?vertices)
                              (m-aristas ?m-aristas) (aristas $?aristas))
  =>
  (retract ?entrada)

  (printout t "--> INICIALIZANDO SISTEMA A PARTIR DE LOS DATOS DE ENTRADA ..." crlf crlf)

  ;DATOS DE INICIALIZACION

  ;Guarda en variables globales el numero de vertices y aristas, necesarios para la inicializacion del sistema.
  (bind ?*n-vertices* ?n-vertices)
  (bind ?*m-aristas* ?m-aristas)

  ;Guarda en una variable global el valor del techo del logaritmo en base 2 de m, necesario para la inicializacion del sistema.
  (bind ?*techo-log2-m* (techo (/ (log ?*m-aristas*) (log 2))))

  ;ESTRUCTURA DE MEMBRANAS

  (assert
    ;La membrana 0 representa al entorno (salida) y requiere ser inicializada con los elementos que codifican una instancia
    ; del problema 3-COL. Ademas contiene el resto de elementos necesarios para el sistema. [0 - {yes, no}]
    (membrana (etiqueta 0)
              (identificador 0)
              (contenido , b , D , E , e , t , S , N , z ,))

    (membrana (etiqueta 1) ;El estado inicial de la membrana 1 es igual para cualquier instancia del problema.
              (identificador 1)
              (contenido , 1 a 1 , 1 b , 1 c 1 , 1 yes , 1 no ,))

    ;La membrana 2 contiene, entre otros, los elementos de entrada que codifican una instancia del problema 3-COL, por lo tanto
    ; tambien requiere ser inicializada con dichos elementos.
    (membrana (etiqueta 2)
              (identificador 2)
              (contenido , 1 D ,)))


  ;REGLAS DEL SISTEMA P

  (assert ;COMUNICACION (1 <-> 0)
          (regla-comunicacion (etiqueta-izquierda 1)  ;r22
                              (elemento1-izquierda b)
                              (elemento2-izquierda t)
                              (etiqueta-derecha 0)
                              (elemento1-derecha S))

          (regla-comunicacion (etiqueta-izquierda 1) ;r23
                              (elemento1-izquierda S)
                              (elemento2-izquierda yes)
                              (etiqueta-derecha 0))

          (regla-comunicacion (etiqueta-izquierda 1) ;r24
                              (elemento1-izquierda a (+ (* 2 ?*n-vertices*) ?*techo-log2-m* 12))
                              (elemento2-izquierda b)
                              (etiqueta-derecha 0)
                              (elemento1-derecha N))

          (regla-comunicacion (etiqueta-izquierda 1) ;r25
                              (elemento1-izquierda N)
                              (elemento2-izquierda no)
                              (etiqueta-derecha 0)))

  (assert ;COMUNICACION (2 <-> 0)
          (regla-comunicacion (etiqueta-izquierda 2) ;r6
                              (elemento1-izquierda c (+ (* 2 ?*n-vertices*) 1))
                              (etiqueta-derecha 0)
                              (elemento1-derecha d 1)
                              (elemento2-derecha E))

          (regla-comunicacion (etiqueta-izquierda 2) ;r8
                              (elemento1-izquierda E)
                              (etiqueta-derecha 0)
                              (elemento1-derecha e)
                              (elemento2-derecha f 2))

          (regla-comunicacion (etiqueta-izquierda 2) ;r19
                              (elemento1-izquierda e)
                              (elemento2-izquierda z)
                              (etiqueta-derecha 0))

          (regla-comunicacion (etiqueta-izquierda 2) ;r20
                              (elemento1-izquierda f (+ ?*techo-log2-m* 7))
                              (elemento2-izquierda e)
                              (etiqueta-derecha 0)
                              (elemento1-derecha t))

          ;COMUNICACION (1 <-> 2)
          (regla-comunicacion (etiqueta-izquierda 1) ;r5
                              (elemento1-izquierda c (+ (* 2 ?*n-vertices*) 1))
                              (etiqueta-derecha 2)
                              (elemento1-derecha D))

          ;COMUNICACION (2 <-> 1)
          (regla-comunicacion (etiqueta-izquierda 2) ;r21
                              (elemento1-izquierda t)
                              (etiqueta-derecha 1)))

  ;VERTICES Y ARISTAS

  ;Hechos para la inicializacion de vertices y aristas.
  (assert (inicializa-vertices ?n-vertices $?vertices) ;(, A 1 , A 2 , ... , A n ,)
          (inicializa-aristas ?m-aristas $?aristas))   ;(, A 1 2 , A 1 3 , ... , A i j ,) con 1 <= i < j <= n

  ;CONTADORES

  ;Hechos para la inicializacion de los distintos tipos de contadores del sistema.
  (assert (inicializa-contadores a)
          (inicializa-contadores c)
          (inicializa-contadores d)
          (inicializa-contadores f))

)

(defrule inicializacion-vertices "introduce en el sistema los elementos referentes a los vertices"
  (declare (salience 99)) ;Se inicializan en primer lugar.

  (estado inicializacion)

  ?iv <- (inicializa-vertices ?pendientes $?vi , A ?i , $?vf)

  ?entorno <- (membrana (etiqueta 0)
                        (contenido $?c0))

  ?entrada <- (membrana (etiqueta 2)
                        (contenido $?c2))

  =>
  (retract ?iv)

  (modify ?entorno (contenido $?c0 A ?i , R ?i , T ?i , B ?i , G ?i , RC ?i , BC ?i , GC ?i ,))
  (modify ?entrada (contenido $?c2 1 A ?i ,))

  ;REGLAS ASOCIADAS A LOS VERTICES

  ;DIVISION
  (assert (regla-division (etiqueta 2) ;r1i
                           (elemento-izquierda A ?i)
                           (elemento1-derecha R ?i)
                           (elemento2-derecha T ?i))

          (regla-division (etiqueta 2) ;r2i
                           (elemento-izquierda T ?i)
                           (elemento1-derecha B ?i)
                           (elemento2-derecha G ?i)))

   ;COMUNICACION (2 <-> 0)
   (assert (regla-comunicacion (etiqueta-izquierda 2) ;r16i
                              (elemento1-izquierda R ?i)
                              (elemento2-izquierda RC ?i)
                              (etiqueta-derecha 0)
                              (elemento1-derecha z))

          (regla-comunicacion (etiqueta-izquierda 2) ;r17i
                              (elemento1-izquierda B ?i)
                              (elemento2-izquierda BC ?i)
                              (etiqueta-derecha 0)
                              (elemento1-derecha z))

          (regla-comunicacion (etiqueta-izquierda 2) ;r18i
                              (elemento1-izquierda G ?i)
                              (elemento2-izquierda GC ?i)
                              (etiqueta-derecha 0)
                              (elemento1-derecha z)))

  ;Comprueba si existen vertices que no han sido procesados.
  (if (> ?pendientes 1)
    then (assert (inicializa-vertices (- ?pendientes 1) $?vi , $?vf))

    else (assert (vertices))) ;Se han incluido todos los elementos de los vertices en las membranas correspondientes.

)

(defrule inicializacion-aristas "introduce en el sistema los elementos referentes a las aristas"
    (declare (salience 97)) ;Se inicializan en ultimo lugar.

    (estado inicializacion)

    ?ia <- (inicializa-aristas ?pendientes $?ai , A ?i ?j , $?af)

    ?entorno <- (membrana (etiqueta 0)
                          (contenido $?c0))

    ?entrada <- (membrana (etiqueta 2)
                          (contenido $?c2))

  =>
  (retract ?ia)

  (modify ?entorno (contenido $?c0 P ?i ?j , PC ?i ?j , R ?i ?j , B ?i ?j , G ?i ?j ,))
  (modify ?entrada (contenido $?c2 1 A ?i ?j ,))

  ;REGLAS ASOCIADAS A LAS ARISTAS

  ;COMUNICACION (2 <-> 0)
  (assert (regla-comunicacion (etiqueta-izquierda 2)  ;r10ij
                              (elemento1-izquierda d (+ ?*techo-log2-m* 1))
                              (elemento2-izquierda A ?i ?j)
                              (etiqueta-derecha 0)
                              (elemento1-derecha P ?i ?j))

          (regla-comunicacion (etiqueta-izquierda 2) ;r11ij
                              (elemento1-izquierda P ?i ?j)
                              (etiqueta-derecha 0)
                              (elemento1-derecha R ?i ?j)
                              (elemento2-derecha PC ?i ?j))

          (regla-comunicacion (etiqueta-izquierda 2) ;r12ij
                              (elemento1-izquierda PC ?i ?j)
                              (etiqueta-derecha 0)
                              (elemento1-derecha B ?i ?j)
                              (elemento2-derecha G ?i ?j))

          (regla-comunicacion (etiqueta-izquierda 2) ;r13ij
                              (elemento1-izquierda R ?i)
                              (elemento2-izquierda R ?i ?j)
                              (etiqueta-derecha 0)
                              (elemento1-derecha R ?i)
                              (elemento2-derecha RC ?j))

          (regla-comunicacion (etiqueta-izquierda 2) ;r14ij
                              (elemento1-izquierda B ?i)
                              (elemento2-izquierda B ?i ?j)
                              (etiqueta-derecha 0)
                              (elemento1-derecha B ?i)
                              (elemento2-derecha BC ?j))

          (regla-comunicacion (etiqueta-izquierda 2) ;r15ij
                              (elemento1-izquierda G ?i)
                              (elemento2-izquierda G ?i ?j)
                              (etiqueta-derecha 0)
                              (elemento1-derecha G ?i)
                              (elemento2-derecha GC ?j)))

  ;Comprueba si hay aristas que no han sido procesadas.
  (if (> ?pendientes 1)
    then (assert (inicializa-aristas (- ?pendientes 1) $?ai , $?af))

    else (assert (aristas))) ;Se han incluido todos los elementos de las aristas en las membranas correspondientes.

)

(defrule inicializacion-contadores "genera los contadores necesarios en el entorno"
  (declare (salience 98)) ;Se inicializan en segundo lugar.

  (estado inicializacion)

  ?ic <- (inicializa-contadores ?tipo)

  ?entorno <- (membrana (etiqueta 0)
                        (contenido $?c0))

  =>
  (retract ?ic)

  (switch ?tipo
      (case a ;1 ... 2n + [log2(m)] + 12
        then (bind ?indice-a 1)
             (bind ?contadores (create$ ?tipo ?indice-a ,))
             (bind ?limite-a (+ (*  2 ?*n-vertices*) ?*techo-log2-m* 12))

             ;Genera la lista de elementos referentes al contador correspondiente.
             (while (< ?indice-a ?limite-a)

                ;REGLAS ASOCIADA AL CONTADOR a CON INDICE i

                ;COMUNICACION (1 <-> 0)
                (assert (regla-comunicacion (etiqueta-izquierda 1) ;r3i
                                            (elemento1-izquierda a ?indice-a)
                                            (etiqueta-derecha 0)
                                            (elemento1-derecha a (+ ?indice-a 1))))

                (bind ?indice-a (+ ?indice-a 1))
                (bind ?contadores (insert$ ?contadores 1 ?tipo ?indice-a ,))))

      (case c ;1 ... 2n + 1
        then (bind ?indice-c 1)
             (bind ?contadores (create$ ?tipo ?indice-c ,))
             (bind ?limite-c (+ (* 2 ?*n-vertices*) 1))
             (while (< ?indice-c ?limite-c)

                ;REGLAS ASOCIADA AL CONTADOR c CON INDICE i

                ;COMUNICACION (1 <-> 0)
                (assert (regla-comunicacion (etiqueta-izquierda 1) ;r4i
                                            (elemento1-izquierda c ?indice-c)
                                            (etiqueta-derecha 0)
                                            (elemento1-derecha c (+ ?indice-c 1))
                                            (elemento2-derecha c (+ ?indice-c 1))))

                (bind ?indice-c (+ ?indice-c 1))
                (bind ?contadores (insert$ ?contadores 1 ?tipo ?indice-c ,))))

      (case d ;1 ... [log2(m)] + 1
        then (bind ?indice-d 1)
             (bind ?contadores (create$ ?tipo ?indice-d ,))
             (bind ?limite-d (+ ?*techo-log2-m* 1))
             (while (< ?indice-d ?limite-d)

                ;REGLAS ASOCIADA AL CONTADOR d CON INDICE i

                ;COMUNICACION (2 <-> 0)
                (assert (regla-comunicacion (etiqueta-izquierda 2) ;r7i
                                            (elemento1-izquierda d ?indice-d)
                                            (etiqueta-derecha 0)
                                            (elemento1-derecha d (+ ?indice-d 1))
                                            (elemento2-derecha d (+ ?indice-d 1))))

                (bind ?indice-d (+ ?indice-d 1))
                (bind ?contadores (insert$ ?contadores 1 ?tipo ?indice-d ,))))

      (case f ;2 ... [log2(m)] + 7
        then (bind ?indice-f 2)
             (bind ?contadores (create$ ?tipo ?indice-f ,))
             (bind ?limite-f (+ ?*techo-log2-m* 7))
             (while (< ?indice-f ?limite-f)

                ;REGLAS ASOCIADA AL CONTADOR f CON INDICE i

                ;COMUNICACION (2 <-> 0)
                (assert (regla-comunicacion (etiqueta-izquierda 2) ;r9i
                                           (elemento1-izquierda f ?indice-f)
                                           (etiqueta-derecha 0)
                                           (elemento1-derecha f (+ ?indice-f 1))))

                (bind ?indice-f (+ ?indice-f 1))
                (bind ?contadores (insert$ ?contadores 1 ?tipo ?indice-f ,)))))

  (modify ?entorno (contenido $?c0 ?contadores))
  (assert (contadores ?tipo)) ;Se han incluido todos los contadores del tipo indicado.

)

(defrule inicia-computacion "realiza los cambios pertinenetes en el sistema para que empiece la computacion"

  ?estado <- (estado inicializacion)

  ;Se han inicializado todos los componentes del sistema.
  ?vertices <- (vertices)
  ?contadores-a <- (contadores a)
  ?contadores-c <- (contadores c)
  ?contadores-d <- (contadores d)
  ?contadores-f <- (contadores f)
  ?aristas <- (aristas)

  ;Membranas en fase de inicializacion.
  (membrana (etiqueta 0) ;Entorno
            (contenido $?c0))

  (membrana (etiqueta 1)
            (contenido $?c1))

  (membrana (etiqueta 2) ;Entrada
            (contenido $?c2))

  =>
  (retract ?estado ?vertices ?contadores-a ?contadores-c ?contadores-d ?contadores-f ?aristas)

  (printout t "--> COMIENZA LA COMPUTACION ..." crlf crlf)


  (printout t "  [NOTA: En el entorno se suponen un numero suficiente de copias de cada elemento para realizar el proceso    ]" crlf)
  (printout t "  [       Por tanto su contenido no es alterado hasta que se introduzca en el la respuesta final. En el resto ]" crlf)
  (printout t "  [       de membranas cada elemento lleva un numero delante que indica el numero de copias del mismo en la   ]" crlf)
  (printout t "  [       configuracion correspondiente.                                                                      ]" crlf crlf)


  (printout t "   CONFIGURACION INICIAL:" crlf)
  (printout t "   Entorno " $?c0  crlf)
  (printout t "   M1.1 " $?c1 crlf) ;Membrana 1 con identificador 1.
  (printout t "   Entrada " $?c2 crlf crlf)

  (assert (estado transicion))

  ;Incluye copias de las membranas 0, 1 y 2 con el indice de la configuracion siguiente.

  ;Las copias con el indice de la configuracion siguiente reflejaran los cambios producidos en las membranas con configuracion
  ; actual a partir de la aplicacion de reglas. Las membranas actuales actualizan tambien su contenido en funcion de la regla aplicada
  ; para evitar la aplicacion de nuevas reglas debidas a un elemento que ya ha reaccionado a una regla.
  ;
  ;En un paso de la computacion, cada elemento de una membrana con la configuracion actual puede ser afectado unicamente por una regla
  ; (si hay varias que puedan aplicarse se escogen de manera no determinista) y todo elemento de la membrana al que se le pueda aplicar
  ; una regla debe verse afectado por la misma. Un elemento obtenido a partir de la aplicacion de una regla no puede activar una regla
  ; hasta el siguiente paso de la computacion, es decir, hasta la siguiente configuracion del sistema.

  (assert (membrana (etiqueta 0)
                    (identificador 0)
                    (configuracion 2)
                    (contenido $?c0))

          (membrana (etiqueta 1)
                    (identificador 1)
                    (configuracion 2)
                    (contenido $?c1))

          (membrana (etiqueta 2)
                    (identificador 2)
                    (configuracion 2)
                    (contenido $?c2)))

)

(defrule finaliza-transicion "comprueba si queda alguna regla de comunicacion por aplicar en la configuracion actual"

  ?estado <- (estado transicion)

  (paso-actual ?pactual)
  (paso-siguiente ?psiguiente)

  ;Comprueba que no queda ninguna regla de comunicacion que se pueda aplicar.

  (not (and
      (regla-comunicacion (etiqueta-izquierda ?etiqueta-izquierda)
                          (elemento1-izquierda $?elemento1-izquierda)
                          (elemento2-izquierda $?elemento2-izquierda)
                          (etiqueta-derecha ?etiqueta-derecha)
                          (elemento1-derecha $?elemento1-derecha)
                          (elemento2-derecha $?elemento2-derecha))

      ;PARTE IZQUIERDA DE LA REGLA
      (membrana (etiqueta ?etiqueta-izquierda)
                (identificador ?id-izquierda)
                (configuracion ?pactual)
                (contenido $?ca-izquierda))

      (membrana (etiqueta ?etiqueta-izquierda)
                (identificador ?id-izquierda)
                (configuracion ?psiguiente)
                (contenido $?cs-izquierda))

      (or ;ENVIA DOS ELEMENTOS IGUALES
       (and (test (eq $?elemento1-izquierda $?elemento2-izquierda))
            (test (existe-elemento $?ca-izquierda 2 $?elemento1-izquierda))
            (test (existe-elemento $?cs-izquierda 2 $?elemento1-izquierda)))

          ;ENVIA DOS ELEMENTOS DISTINTOS
       (and (test (neq $?elemento1-izquierda $?elemento2-izquierda))
            (test (existe-elemento $?ca-izquierda 1 $?elemento1-izquierda))
            (test (existe-elemento $?cs-izquierda 1 $?elemento1-izquierda))
            (test (existe-elemento $?ca-izquierda 1 $?elemento2-izquierda))
            (test (existe-elemento $?cs-izquierda 1 $?elemento2-izquierda))))


      ;PARTE DERECHA DE LA REGLA
      (membrana (etiqueta ?etiqueta-derecha)
                              (identificador ?id-derecha)
                              (configuracion ?pactual)
                              (contenido $?ca-derecha))

      (membrana (etiqueta ?etiqueta-derecha)
                (identificador ?id-derecha)
                (configuracion ?psiguiente)
                (contenido $?cs-derecha))


      (or
        (test (= ?etiqueta-derecha 0)) ;Si se trata del entorno, este siempre tiene los elementos necesarios.

        (and ;ENVIA DOS ELEMENTOS IGUALES
          (test (<> ?etiqueta-derecha 0))
          (test (eq $?elemento1-derecha $?elemento2-derecha))
          (test (existe-elemento $?ca-derecha 2 $?elemento1-derecha))
          (test (existe-elemento $?cs-derecha 2 $?elemento1-derecha)))

        (and ;ENVIA DOS ELEMENTOS DISTINTOS
          (test (<> ?etiqueta-derecha 0))
          (test (neq $?elemento1-derecha $?elemento2-derecha))
          (test (existe-elemento $?ca-derecha 1 $?elemento1-derecha))
          (test (existe-elemento $?cs-derecha 1 $?elemento1-derecha))
          (test (existe-elemento $?ca-derecha 1 $?elemento2-derecha))
          (test (existe-elemento $?cs-derecha 1 $?elemento2-derecha))))))

  =>
  (retract ?estado)

  ;Cambia el estado del sistema para realizar las acciones necesarias con objeto
  ; de preparar el sistema para el siguiente paso de la computacion.

  (assert (estado actualizacion))

)

(defrule quita-membranas-actuales "quita las membranas con el indice de la configuracion actual"
  (estado actualizacion)
  (paso-actual ?pactual)

  ?actual <- (membrana  (etiqueta ?etiqueta)
                        (identificador ?id)
                        (configuracion ?pactual))

  =>
  (retract ?actual)
  (assert (imprime-membrana ?id))

)

(defrule imprime-regla-aplicada "imprime las reglas aplicadas durante el paso actual de la computacion"
  (estado actualizacion)
  (paso-actual ?pactual)

  (not (membrana (configuracion ?pactual)))

  ?imprime <- (imprime-regla-aplicada $?regla)

  =>
  (retract ?imprime)
  (printout t "     Aplica Regla > " $?regla  crlf)

)

(defrule imprime-entorno "imprime por pantalla el contenido del entorno al final de una transicion"
  (declare (salience 99))

  (estado actualizacion)
  (paso-actual ?pactual)
  (paso-siguiente ?psiguiente)

  (not (membrana (configuracion ?pactual)))
  (not (imprime-regla-aplicada $?))

  ?imprime <- (imprime-membrana 0)

  ?entorno <- (membrana (etiqueta 0)
                        (identificador 0)
                        (configuracion ?psiguiente)
                        (contenido $?c))

  =>
  (retract ?imprime)
  (printout t crlf)
  (printout t "   CONFIGURACION " ?psiguiente ":" crlf)
  (printout t "   Entorno " $?c  crlf)

)

(defrule imprime-membrana-1 "imprime por pantalla el contenido de la membrana etiquetada por uno al final de la transicion"
  (declare (salience 98))

  (estado actualizacion)
  (paso-actual ?pactual)
  (paso-siguiente ?psiguiente)

  (not (membrana (configuracion ?pactual)))
  (not (imprime-regla-aplicada $?))

  ?imprime <- (imprime-membrana 1)

  ?membrana1 <- (membrana (etiqueta 1)
                          (identificador 1)
                          (configuracion ?psiguiente)
                          (contenido $?c))

  =>
  (retract ?imprime)
  (printout t "   M1.1 " $?c  crlf)

)

(defrule imprime-membrana-2 "imprime el contenido de las membranas etiquetadas por dos al final de la transicion"
  (declare (salience 97))

  (estado actualizacion)
  (paso-actual ?pactual)
  (paso-siguiente ?psiguiente)

  (not (membrana (configuracion ?pactual)))
  (not (imprime-regla-aplicada $?))

  ?imprime <- (imprime-membrana ?id&~0&~1)

  ?membrana <- (membrana (etiqueta 2)
                         (identificador ?id)
                         (configuracion ?psiguiente)
                         (contenido $?c))

  =>
  (retract ?imprime)
  (printout t "   M2." ?id " " $?c  crlf)

)

(defrule inserta-membranas-siguientes "inserta las copias de las membranas necesarias para la siguiente paso"
  (estado actualizacion)
  (paso-actual ?pactual)
  (paso-siguiente ?psiguiente)

  (not (membrana (configuracion ?pactual)))

  ;Se han terminado de imprimir los datos de la transicion actual.
  (not (imprime-membrana ?))
  (not (imprime-regla-aplicada $?))

  ;El sistema no se encuenta en la configuracion de parada.
  (not (membrana (etiqueta 0)
                 (configuracion ?psiguiente)
                 (contenido $? , yes|no , $?)))


  ?siguiente <- (membrana (etiqueta ?etiqueta)
                          (identificador ?id)
                          (configuracion ?psiguiente)
                          (contenido $?c))

  =>
  ;Introduce copia con el indice de la siguiente configuracion.
  (assert (membrana (etiqueta ?etiqueta)
                    (identificador ?id)
                    (configuracion (+ ?psiguiente 1))
                    (contenido $?c)))

)

(defrule siguiente-configuracion "pasa el sistema a la siguiente configuracion"
  ?pa <- (paso-actual ?pactual)
  ?ps <- (paso-siguiente ?psiguiente)

  ?estado <- (estado actualizacion)

  ;Verifica que toda membrana tiene su copia con el indice de la configuracion siguiente a la misma.
  (forall (membrana (identificador ?id)
                    (configuracion ?psiguiente))

          (membrana (identificador ?id)
                    (configuracion ?siguiente&:(= ?siguiente (+ ?psiguiente 1)))))

  =>
  (retract ?pa ?ps ?estado)
  (assert (estado transicion))
  (assert (paso-actual ?psiguiente)
          (paso-siguiente (+ ?psiguiente 1)))

  (printout t crlf)

)

(defrule finaliza-computacion "termina la computacion si se ha llegado a una configuracion de parada"

  ?estado <- (estado actualizacion)

  (paso-actual ?pactual)
  (paso-siguiente ?psiguiente)

  (not (membrana (configuracion ?pactual)))

  ;Se han terminado de imprimir los datos de la transicion actual.
  (not (imprime-membrana ?))
  (not (imprime-regla-aplicada $?))

  (membrana (etiqueta 0)
            (configuracion ?psiguiente)
            (contenido $? , ?res&yes|no , $?))

  =>
  (retract ?estado)
  (assert (estado respuesta))

  (printout t crlf)

  (if (eq ?res yes)
    then (printout t "--> LA INSTANCIA DEL PROBLEMA 3-COL INDICADADA SI PUEDE SER COLOREADA CON 3 COLORES" crlf crlf)
    else (printout t "--> LA INSTANCIA DEL PROBLEMA 3-COL INDICADADA NO PUEDE SER COLOREADA CON 3 COLORES" crlf crlf))

)

;DIVISION

;Si se aplica una regla de division, en el mismo paso de la transicion no podra aplicarse ninguna otra regla ya sea
; de division o de comunicacion. Este hecho se controla de manera que al aplicar la regla de division se eliminan las membranas
; con configuracion actual por lo que no podra volverse a interactuar con ella hasta el siguiente paso de la transicion.

(defrule division "crea dos nuevas membranas en sustitucion de una existente y a partir de una regla de division concreta"

  ;Estado actual del sistema
  (estado transicion)

  (paso-actual ?pactual)
  (paso-siguiente ?psiguiente)

  ;Selecciona los elementos que definen la regla de division
  (regla-division (etiqueta ?etiqueta&~0&~1)
                  (elemento-izquierda $?elemento-izquierda)
                  (elemento1-derecha $?elemento1-derecha)
                  (elemento2-derecha $?elemento2-derecha))

  ?actual <- (membrana (etiqueta ?etiqueta)
                       (identificador ?id)
                       (configuracion ?pactual)
                       (contenido $? , ? $?elemento-izquierda , $?))

  ?siguiente <- (membrana (identificador ?id)
                          (configuracion ?psiguiente)
                          (contenido $?ci , ? $?elemento-izquierda , $?cf))

  =>
  (retract ?actual ?siguiente)

  ;Para que no se descuadren los indices de los contadores del sistema, es preciso disponer de las copias suficientes de cada
  ; simbolo correspondiente a cada color, Ri , Bi y Gi en la asignacion de los mismos a una celula (posible solucion). La regla
  ; de comunicacion a partir de la cual se obtienen las versiones complementadas de dichos simbolos para cada posible solucion,
  ; necesita un numero de pasos determinados en funcion de las aristas que involucre a cada vertice, de manera que, en dichos pasos
  ; no se incremente ningun contador del sistema. Esto se debe a que, en el intercambio Ri Rij <-> Ri RCj de la regla correspondiente,
  ; no se puede volver a aplicar una regla sobre Ri pues el Ri que introduce la parte derecha es otro y por tanto no puede ser afectado
  ; hasta el siguiente paso segun el modelo de computacion celular basado en tejidos. Entonces, como solucion, se ha optado por
  ; introducir un numero de copias igual a el numero de vertices del problema en el momento de incluir un simbolo que asigne un color a
  ; un vertice. De esta manera, se controla cualquier numero de aristas que involucren a un mismo vertice, pues un vertice nunca tendra
  ; mas aristas que vertices existen en el grafo que codifica el problema. Y asi, la obtencion  de las versiones complementadas de los
  ; colores podran obtenerse en un unico paso sin descuadrar el valor de los contadores del sistema y permitiendo llegar a la solucion
  ; de manera satisfactoria segun el conjunto de reglas que definen el sistema.

  (assert (membrana (etiqueta ?etiqueta)
                    (identificador (+ ?*id* 1))
                    (configuracion ?psiguiente)
                    (contenido $?ci , ?*n-vertices* $?elemento1-derecha , $?cf)))

  (if (member$ T $?elemento2-derecha)
    then (assert (membrana (etiqueta ?etiqueta)
                           (identificador (+ ?*id* 2))
                           (configuracion ?psiguiente)
                           (contenido $?ci , 1 $?elemento2-derecha , $?cf)))

    else (assert (membrana (etiqueta ?etiqueta)
                           (identificador (+ ?*id* 2))
                           (configuracion ?psiguiente)

                           (contenido $?ci , ?*n-vertices* $?elemento2-derecha , $?cf))))

  ;Hechos para imprimir las membranas al finalizar la transicion entre configuraciones.
  (assert (imprime-membrana (+ ?*id* 1))
          (imprime-membrana (+ ?*id* 2)))

  ;Hecho para imprimir las reglas aplicadas al finalizar la transicion entre configuraciones.
  (assert (imprime-regla-aplicada ?etiqueta [ $?elemento-izquierda ] > [ $?elemento1-derecha ][ $?elemento2-derecha ]))

  ;Incrementa el valor referencia del identificador de membranas.
  (bind ?*id* (+ ?*id* 2))

)

;COMUNICACION

;En un paso de la transicion pueden aplicarse varias reglas de comunicacion en caso de que en la membrana existan elementos que activen
; dichas reglas. Los elementos obtenidos de la aplicacion de una regla no se tienen en cuenta para la activacion de reglas hasta el
; siguiente paso. La longitud maxima de una regla es de cuatro, es decir, como maximo se envian dos elementos desde ambas membranas
; involucradas en la comunicacion.

(defrule comunicacion

  ;Estado actual del sistema
  (estado transicion)

  (paso-actual ?pactual)
  (paso-siguiente ?psiguiente)

  ;Regla que especifica la comunicacion a realizar.
  (regla-comunicacion (etiqueta-izquierda ?etiqueta-izquierda&~0)
                      (elemento1-izquierda $?elemento1-izquierda) ;Este elemento nunca puede ser vacio.
                      (elemento2-izquierda $?elemento2-izquierda)
                      (etiqueta-derecha ?etiqueta-derecha)
                      (elemento1-derecha $?elemento1-derecha) ;Si este elemento es vacio el segundo tambien lo es.
                      (elemento2-derecha $?elemento2-derecha))

  ;PARTE IZQUIERDA DE LA REGLA
  ?mi-actual <- (membrana (etiqueta ?etiqueta-izquierda)
                          (identificador ?id-izquierda)
                          (configuracion ?pactual)
                          (contenido $?ca-izquierda))

  ?mi-siguiente <- (membrana (etiqueta ?etiqueta-izquierda)
                             (identificador ?id-izquierda)
                             (configuracion ?psiguiente)
                             (contenido $?cs-izquierda))

  ;Comprueba si existen los elementos necesarios en la membrana especificada en la parte izquierda de la regla.

  (or ;ENVIA DOS ELEMENTOS IGUALES
    (and (test (eq $?elemento1-izquierda $?elemento2-izquierda))
         (test (existe-elemento $?ca-izquierda 2 $?elemento1-izquierda))
         (test (existe-elemento $?cs-izquierda 2 $?elemento1-izquierda)))

      ;ENVIA DOS ELEMENTOS DISTINTOS
    (and (test (neq $?elemento1-izquierda $?elemento2-izquierda))
         (test (existe-elemento $?ca-izquierda 1 $?elemento1-izquierda))
         (test (existe-elemento $?cs-izquierda 1 $?elemento1-izquierda))
         (test (existe-elemento $?ca-izquierda 1 $?elemento2-izquierda))
         (test (existe-elemento $?cs-izquierda 1 $?elemento2-izquierda))))


  ;PARTE DERECHA DE LA REGLA
  ?md-actual <- (membrana (etiqueta ?etiqueta-derecha)
                          (identificador ?id-derecha)
                          (configuracion ?pactual)
                          (contenido $?ca-derecha))

  ?md-siguiente <- (membrana (etiqueta ?etiqueta-derecha)
                             (identificador ?id-derecha)
                             (configuracion ?psiguiente)
                             (contenido $?cs-derecha))

  ;Comprueba si existen los elementos necesarios en la membrana especificada en la parte derecha de la regla

  (or
    (test (= ?etiqueta-derecha 0)) ;Si se trata del entorno, este siempre tiene los elementos necesarios.

    (and ;ENVIA DOS ELEMENTOS IGUALES
      (test (<> ?etiqueta-derecha 0))
      (test (eq $?elemento1-derecha $?elemento2-derecha))
      (test (existe-elemento $?ca-derecha 2 $?elemento1-derecha))
      (test (existe-elemento $?cs-derecha 2 $?elemento1-derecha)))

    (and ;ENVIA DOS ELEMENTOS DISTINTOS
      (test (<> ?etiqueta-derecha 0))
      (test (neq $?elemento1-derecha $?elemento2-derecha))
      (test (existe-elemento $?ca-derecha 1 $?elemento1-derecha))
      (test (existe-elemento $?cs-derecha 1 $?elemento1-derecha))
      (test (existe-elemento $?ca-derecha 1 $?elemento2-derecha))
      (test (existe-elemento $?cs-derecha 1 $?elemento2-derecha))))

  =>
  ;Asignacion de variables para que el contenido vaya actualizandose adecuadamente en cada caso.
  (bind ?contenido-mi-actual $?ca-izquierda)
  (bind ?contenido-mi-siguiente $?cs-izquierda)
  (bind ?contenido-md-actual $?ca-derecha)
  (bind ?contenido-md-siguiente $?cs-derecha)

  ;EMISION MEMBRANA IZQUIERDA
  (if (eq $?elemento1-izquierda $?elemento2-izquierda)
    then (bind ?contenido-mi-actual    (elimina-elementos ?contenido-mi-actual 2 $?elemento1-izquierda))
         (bind ?contenido-mi-siguiente (elimina-elementos ?contenido-mi-siguiente 2 $?elemento1-izquierda))

         ;El entorno permanece inalterado segun el supuesto inicial de que contiene todas las copias suficientes
         ; que precise el sistema de cada elemento.

         (if (<> ?etiqueta-derecha 0)
          then (bind ?contenido-md-siguiente (agrega-elementos ?contenido-md-siguiente 2 $?elemento1-izquierda)))


    else (bind ?contenido-mi-actual    (elimina-elementos ?contenido-mi-actual 1 $?elemento1-izquierda))
         (bind ?contenido-mi-actual    (elimina-elementos ?contenido-mi-actual 1 $?elemento2-izquierda))
         (bind ?contenido-mi-siguiente (elimina-elementos ?contenido-mi-siguiente 1 $?elemento1-izquierda))
         (bind ?contenido-mi-siguiente (elimina-elementos ?contenido-mi-siguiente 1 $?elemento2-izquierda))

         (if (<> ?etiqueta-derecha 0)
          then (bind ?contenido-md-siguiente (agrega-elementos ?contenido-md-siguiente 1 $?elemento1-izquierda))
               (bind ?contenido-md-siguiente (agrega-elementos ?contenido-md-siguiente 1 $?elemento2-izquierda))))

   ;EMISION MEMBRANA DERECHA
   (if (eq $?elemento1-derecha $?elemento2-derecha)
     then (if (<> ?etiqueta-derecha 0)
            then (bind ?contenido-md-actual    (elimina-elementos ?contenido-md-actual 2 $?elemento1-derecha))
                 (bind ?contenido-md-siguiente (elimina-elementos ?contenido-md-siguiente 2 $?elemento1-derecha)))

          (bind ?contenido-mi-siguiente (agrega-elementos ?contenido-mi-siguiente 2 $?elemento2-derecha))

     else (if (<> ?etiqueta-derecha 0)
            then (bind ?contenido-md-actual    (elimina-elementos ?contenido-md-actual 1 $?elemento1-derecha))
                 (bind ?contenido-md-actual    (elimina-elementos ?contenido-md-actual 1 $?elemento2-derecha))
                 (bind ?contenido-md-siguiente (elimina-elementos ?contenido-md-siguiente 1 $?elemento1-derecha))
                 (bind ?contenido-md-siguiente (elimina-elementos ?contenido-md-siguiente 1 $?elemento2-derecha)))

          (bind ?contenido-mi-siguiente (agrega-elementos ?contenido-mi-siguiente 1 $?elemento1-derecha))
          (bind ?contenido-mi-siguiente (agrega-elementos ?contenido-mi-siguiente 1 $?elemento2-derecha)))


    ;Modifica el contenido de cada membrana producto de la comunicacion.
    (modify ?mi-actual    (contenido ?contenido-mi-actual))
    (modify ?mi-siguiente (contenido ?contenido-mi-siguiente))

    (if (<> ?etiqueta-derecha 0)
      then  (modify ?md-actual    (contenido ?contenido-md-actual))
            (modify ?md-siguiente (contenido ?contenido-md-siguiente))

      ;Si se trata del entorno y el elemento a introducir es la respuesta, ha de incluirse en el mismo.
      else (if (or (member$ yes $?elemento2-izquierda) (member$ no $?elemento2-izquierda))
             then (modify ?md-siguiente (contenido , $?elemento2-izquierda ?contenido-md-siguiente))))

    ;Hecho para imprimir las reglas aplicadas.
    (assert (imprime-regla-aplicada ?etiqueta-izquierda , $?elemento1-izquierda $?elemento2-izquierda /
                                                      $?elemento1-derecha $?elemento2-derecha , ?etiqueta-derecha))

)
