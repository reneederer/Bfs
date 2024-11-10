namespace App

open Fable.React
open Feliz
open Feliz.Router
open Feliz
open Feliz.UseElmish
open Elmish
open Fable.Core
open Fable.SimpleJson
open System.Text.RegularExpressions
open System
open Fable.React.DrawingCanvas
open Fable.React.DrawingCanvas.Builder
open Feliz
open type Feliz.Html
open Fable.Core.JsInterop
open Browser.Dom
open Browser.Types

module Bfs =
    ///let _ = importAll "mathjax/es5/tex-mml-chtml.js"
    let mathJaxTypeset () =
        emitJsExpr () "MathJax.typeset()"

    type Msg =
        | Next
        | Prev

    type Zustand = int
    type SchreibLesekopf = int
    type SchreibLesekopfBewegung =
        | R = 1
        | L = -1
        | N = 0

    type EingabeZeichen = char
    type BandZeichen = char


    type TuringMachineState =
        { BandZustand : EingabeZeichen list
          SchreibLesekopfPosition : int
          Eingabemenge : EingabeZeichen list
          Bandeingabemenge : BandZeichen list
          F : Zustand list
          Blank : char
          Program : Map<(Zustand * BandZeichen), (Zustand * BandZeichen * SchreibLesekopfBewegung)>
          Zustandsmenge : int list
          Zustand : int
        }
        with
            member this.Next() =
                let zustand, bandZeichen, schreibLesekopfBewegung =
                    try
                        this.Program[this.Zustand, this.BandZustand[this.SchreibLesekopfPosition]]
                    with
                    | _ ->
                        if this.F |> List.contains this.Zustand then
                            window.alert "akzeptiert"
                        else
                            window.alert "nicht akzeptiert"
                        this.Zustand, this.BandZustand[this.SchreibLesekopfPosition], SchreibLesekopfBewegung.N
                { this with
                          Zustand = zustand
                          BandZustand = this.BandZustand |> List.updateAt this.SchreibLesekopfPosition bandZeichen
                          SchreibLesekopfPosition = this.SchreibLesekopfPosition + (int)schreibLesekopfBewegung
                     
                }

    type BefehlszeigerPosition = int
    type SpeicherPosition = int
    type SpeicherPositionReferenz = int
    type SpeicherInhalt = int

    type Befehlszaehler = int

    type Comparison =
        | Eq
        | Gt
        | Lt
        | Ge
        | Le
        with
            member this.Compare(x, y) =
                match this with
                    | Eq -> x = y
                    | Gt -> x > y
                    | Lt -> x < y
                    | Ge -> x >= y
                    | Le -> x <= y
            static member Parse s =
                match s with
                    | "=" -> Eq
                    | ">" -> Gt
                    | "<" -> Lt
                    | ">=" -> Ge
                    | "<=" -> Le
                    | _ ->
                        failwith "Parse error"

    type RegisterMachineCommand =
        | Load of SpeicherPosition
        | Store of SpeicherPosition
        | Add of SpeicherPosition
        | Sub of SpeicherPosition
        | Mult of SpeicherPosition
        | Div of SpeicherPosition
        | CLoad of SpeicherInhalt
        | CAdd of SpeicherInhalt
        | CSub of SpeicherInhalt
        | CMult of SpeicherInhalt
        | CDiv of SpeicherInhalt
        | IndLoad of SpeicherPositionReferenz
        | IndStore of SpeicherPositionReferenz
        | IndAdd of SpeicherPositionReferenz
        | IndSub of SpeicherPositionReferenz
        | IndMult of SpeicherPositionReferenz
        | IndDiv of SpeicherPositionReferenz
        | IfGoto of SpeicherPosition * Comparison * SpeicherPosition * Befehlszaehler
        | Goto of Befehlszaehler
        | NoOp
        with
            static member Parse (s : string) =
                let s =
                    s.Trim()
                     .ToLower()
                     .Replace(",", "")
                     .Replace("-", "")
                     .Replace("_", "")
                     .Replace("  ", " ")
                let m = Regex.Match(s, @"^(\w+)\s+(\d+(\.\d+)?);?$")
                match m.Groups[1].Value with
                    | "load" -> Load (Int32.Parse m.Groups[2].Value)
                    | "store" -> Store (Int32.Parse m.Groups[2].Value)
                    | "add" -> Add (Int32.Parse m.Groups[2].Value)
                    | "sub" ->  Sub (Int32.Parse m.Groups[2].Value)
                    | "mult" -> Mult (Int32.Parse m.Groups[2].Value)
                    | "div" -> Div (Int32.Parse m.Groups[2].Value)
                    | "cload" -> CLoad (Int32.Parse m.Groups[2].Value)
                    | "cadd" -> CAdd (Int32.Parse m.Groups[2].Value)
                    | "csub" -> CSub (Int32.Parse m.Groups[2].Value)
                    | "cmult" -> CMult (Int32.Parse m.Groups[2].Value)
                    | "cdiv" -> CDiv (Int32.Parse m.Groups[2].Value)
                    | "indload" -> IndLoad (Int32.Parse m.Groups[2].Value)
                    | "indstore" -> IndStore (Int32.Parse m.Groups[2].Value)
                    | "indadd" -> IndAdd (Int32.Parse m.Groups[2].Value)
                    | "indsub" -> IndSub (Int32.Parse m.Groups[2].Value)
                    | "indmult" -> IndMult (Int32.Parse m.Groups[2].Value)
                    | "inddiv" -> IndDiv (Int32.Parse m.Groups[2].Value)
                    | "goto" -> Goto (Int32.Parse m.Groups[2].Value)
                    | "noop" -> Goto (Int32.Parse m.Groups[2].Value)
                    | _ ->
                        let m = Regex.Match(s, "^(if|ifgoto)\s+(\d+)\s+(\w+)\s+(\d+)\s+(\d+);?$")
                        if m.Success then
                            IfGoto (Int32.Parse m.Groups[2].Value, Comparison.Parse m.Groups[3].Value, Int32.Parse m.Groups[4].Value, Int32.Parse m.Groups[5].Value)
                        else
                            failwith $"Could not parse {s}"


    type RegisterMachineState =
        { Speicher : int list
          Program : RegisterMachineCommand list
          Befehlszaehler : Befehlszaehler
        }
        with
            member this.SetSpeicher(toPos, fromPos, f) =
                { this with
                    Speicher = this.Speicher |> List.updateAt toPos (f (this.Speicher[toPos], this.Speicher[fromPos]))
                    Befehlszaehler = this.Befehlszaehler + 1
                }

            member this.CSetSpeicher(toPos, value, f) =
                { this with
                    Speicher = this.Speicher |> List.updateAt toPos (f (this.Speicher[toPos], value))
                    Befehlszaehler = this.Befehlszaehler + 1
                }

            member this.IndSetSpeicher(toPos, fromPosRef, f) =
                { this with
                    Speicher = this.Speicher |> List.updateAt toPos (f (this.Speicher[toPos], this.Speicher[(int)this.Speicher[fromPosRef]]))
                    Befehlszaehler = this.Befehlszaehler + 1
                }


            member this.Next() =
                match this.Program[this.Befehlszaehler - 1] with
                    | Load speicherPosition -> this.SetSpeicher(0, speicherPosition, snd)
                    | Store speicherPosition -> this.SetSpeicher(speicherPosition, 0, snd)
                    | Add speicherPosition  -> this.SetSpeicher(0, speicherPosition, (fun (x, y) -> x + y))
                    | Sub speicherPosition -> this.SetSpeicher(0, speicherPosition, (fun (x, y) -> Math.Max(0, x - y)))
                    | Mult speicherPosition -> this.SetSpeicher(0, speicherPosition, (fun (x, y) -> x * y))
                    | Div speicherPosition -> this.SetSpeicher(0, speicherPosition, (fun (x, y) -> (int)(x / y)))
                    | CLoad speicherInhalt -> this.CSetSpeicher(0, speicherInhalt, snd)
                    | CAdd speicherInhalt -> this.CSetSpeicher(0, speicherInhalt, (fun (x, y) -> x + y))
                    | CSub speicherInhalt -> this.CSetSpeicher(0, speicherInhalt, (fun (x, y) -> Math.Max(0, x - y)))
                    | CMult speicherInhalt -> this.CSetSpeicher(0, speicherInhalt, (fun (x, y) -> x * y))
                    | CDiv speicherInhalt -> this.CSetSpeicher(0, speicherInhalt, (fun (x, y) -> (int)(x / y)))
                    | IndLoad speicherPositionReferenz -> this.IndSetSpeicher(0, speicherPositionReferenz, snd)
                    | IndStore speicherPositionReferenz -> this.SetSpeicher((int)this.Speicher[speicherPositionReferenz], 0, snd)
                    | IndAdd speicherPositionReferenz -> this.SetSpeicher(0, (int)this.Speicher[speicherPositionReferenz], (fun (x, y) -> x + y))
                    | IndSub speicherPositionReferenz -> this.SetSpeicher(0, (int)this.Speicher[speicherPositionReferenz], (fun (x, y) -> Math.Max(0, x - y)))
                    | IndMult speicherPositionReferenz -> this.SetSpeicher(0, (int)this.Speicher[speicherPositionReferenz], (fun (x, y) -> x * y))
                    | IndDiv speicherPositionReferenz -> this.SetSpeicher(0, (int)this.Speicher[speicherPositionReferenz], (fun (x, y) -> (int)(x / y)))
                    | IfGoto (pos1, comp, pos2, befehlszaehler) ->
                        if comp.Compare(this.Speicher[pos1], this.Speicher[pos2]) then
                            { this with Befehlszaehler = befehlszaehler }
                        else
                            { this with Befehlszaehler = this.Befehlszaehler + 1 }
                    | Goto befehlszaehler -> { this with Befehlszaehler = befehlszaehler }
                    | NoOp -> this
                

    type State =
        | TuringMachine of TuringMachineState
        | RegisterMachine of RegisterMachineState

    let init() =
        let blank = 'B'
        let eingabemenge = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890 ".ToCharArray() |> List.ofArray
        let tmWoerterGleich =
            TuringMachine
                { BandZustand =
                    let vorher = List.init 1000 (fun i -> blank)
                    let nachher = List.init 2000 (fun i -> blank)
                    let w = "101#101".ToCharArray() |> List.ofArray
                    vorher@w@nachher
                  SchreibLesekopfPosition = 1000
                  Eingabemenge = ['0'; '1'; '#']
                  Bandeingabemenge = ['0'; '1'; 'B'; 'X'; '#']
                  Blank = blank
                  Zustandsmenge = [0;1;2;3;4;5;6;7;8]
                  Zustand = 0
                  F = [ 8 ]
                  Program =
                    [ (0, '0'), (1, 'X', SchreibLesekopfBewegung.R)
                      (0, '1'), (2, 'X', SchreibLesekopfBewegung.R)
                      //(0, '#'), (1, 'X', SchreibLesekopfBewegung.R)
                      //(0, 'B'), (1, 'X', SchreibLesekopfBewegung.R)
                      //(0, 'X'), (1, 'X', SchreibLesekopfBewegung.R)
                      (1, '0'), (1, '0', SchreibLesekopfBewegung.R)
                      (1, '1'), (1, '1', SchreibLesekopfBewegung.R)
                      (1, '#'), (3, '#', SchreibLesekopfBewegung.R)
                      //(1, 'B'), (1, 'X', SchreibLesekopfBewegung.R)
                      //(1, 'X'), (1, 'X', SchreibLesekopfBewegung.R)
                      (2, '0'), (2, '0', SchreibLesekopfBewegung.R)
                      (2, '1'), (2, '1', SchreibLesekopfBewegung.R)
                      (2, '#'), (4, '#', SchreibLesekopfBewegung.R)
                      //(2, 'B'), (1, 'X', SchreibLesekopfBewegung.R)
                      //(2, 'X'), (1, 'X', SchreibLesekopfBewegung.R)
                      (3, '0'), (5, 'X', SchreibLesekopfBewegung.L)
                      //(3, '1'), (1, 'X', SchreibLesekopfBewegung.R)
                      //(3, '#'), (1, 'X', SchreibLesekopfBewegung.R)
                      //(3, 'B'), (1, 'X', SchreibLesekopfBewegung.R)
                      (3, 'X'), (3, 'X', SchreibLesekopfBewegung.R)
                      //(4, '0'), (5, 'X', SchreibLesekopfBewegung.R)
                      (4, '1'), (5, 'X', SchreibLesekopfBewegung.L)
                      //(4, '#'), (1, 'X', SchreibLesekopfBewegung.R)
                      //(4, 'B'), (1, 'X', SchreibLesekopfBewegung.R)
                      (4, 'X'), (4, 'X', SchreibLesekopfBewegung.R)
                      (5, '0'), (5, '0', SchreibLesekopfBewegung.L)
                      (5, '1'), (5, '1', SchreibLesekopfBewegung.L)
                      (5, '#'), (5, '#', SchreibLesekopfBewegung.L)
                      (5, 'B'), (6, 'B', SchreibLesekopfBewegung.R)
                      (5, 'X'), (5, 'X', SchreibLesekopfBewegung.L)
                      (6, '0'), (0, '0', SchreibLesekopfBewegung.N)
                      (6, '1'), (0, '1', SchreibLesekopfBewegung.N)
                      (6, '#'), (7, '#', SchreibLesekopfBewegung.R)
                      (6, 'B'), (8, 'B', SchreibLesekopfBewegung.N)
                      (6, 'X'), (6, 'X', SchreibLesekopfBewegung.R)
                      //(7, '0'), (1, 'X', SchreibLesekopfBewegung.R)
                      //(7, '1'), (1, 'X', SchreibLesekopfBewegung.R)
                      //(7, '#'), (1, 'X', SchreibLesekopfBewegung.R)
                      (7, 'B'), (8, 'B', SchreibLesekopfBewegung.R)
                      (7, 'X'), (7, 'X', SchreibLesekopfBewegung.R)
                      //(8, '0'), (1, 'X', SchreibLesekopfBewegung.R)
                      //(8, '1'), (1, 'X', SchreibLesekopfBewegung.R)
                      //(8, '#'), (1, 'X', SchreibLesekopfBewegung.R)
                      //(8, 'B'), (1, 'X', SchreibLesekopfBewegung.R)
                      //(8, 'X'), (1, 'X', SchreibLesekopfBewegung.R)
                    ]
                    |> Map.ofList
                }
        let tmCounter =
            TuringMachine
                { BandZustand =
                    let vorher = List.init 1000 (fun i -> blank)
                    let nachher = List.init 2000 (fun i -> blank)
                    let w = "".ToCharArray() |> List.ofArray
                    vorher@w@nachher
                  SchreibLesekopfPosition = 1000
                  Eingabemenge = ['0'; '1'; '#']
                  Bandeingabemenge = ['0'; '1'; 'B'; 'X'; '#']
                  Blank = blank
                  Zustandsmenge = [0;1;2;3;4;5;6;7;8]
                  Zustand = 0
                  F = [ 4 ]
                  Program =
                    [ (0, '0'), (0, '0', SchreibLesekopfBewegung.R)
                      (0, '1'), (0, '1', SchreibLesekopfBewegung.R)
                      (0, 'B'), (1, 'B', SchreibLesekopfBewegung.L)

                      (1, '0'), (1, '1', SchreibLesekopfBewegung.L)
                      (1, '1'), (2, '0', SchreibLesekopfBewegung.L)
                      (1, 'B'), (4, 'B', SchreibLesekopfBewegung.N)

                      (2, '0'), (0, '0', SchreibLesekopfBewegung.R)
                      (2, '1'), (0, '1', SchreibLesekopfBewegung.R)
                      (2, 'B'), (3, 'B', SchreibLesekopfBewegung.R)

                      (3, '0'), (0, 'B', SchreibLesekopfBewegung.R)
                      (3, 'B'), (4, '0', SchreibLesekopfBewegung.N)
                      //(4, 'B'), (1, 'B', SchreibLesekopfBewegung.L)
                    ]
                    |> Map.ofList
                }
        (tmCounter, Cmd.none)
        //(RegisterMachine
        //    { Speicher = [0; 176; 0;]@[ for i in 1..1000 do 0 ]
        //      Program =
        //          [ CLoad 10               // 1
        //            Store 5                // 2

        //            Load 1                 // 3
        //            IfGoto (0, Eq, 4, 18)  // 4
        //            CDiv 7                 // 5
        //            Store 2
        //            CMult 7
        //            Store 3
        //            Load 1
        //            Sub 3

        //            IndStore 5
        //            Load 5
        //            CAdd 1
        //            Store 5

        //            Load 2
        //            Store 1
        //            Goto 3
        //            NoOp

        //          ]

        //      Befehlszaehler = 1
        //    }, Cmd.none)

    let update msg state =
        match state, msg with
        | TuringMachine tm, Next ->
            let json =
                try
                    SimpleJson.stringify state
                with
                | e ->
                    printfn $"{e}"
                    ""
            
            TuringMachine (tm.Next()), Cmd.none
        | TuringMachine tm, Prev -> state, Cmd.none
        | RegisterMachine rm, Prev -> state, Cmd.none
        | RegisterMachine rm, Next ->
            RegisterMachine (rm.Next()), Cmd.none

    [<ReactComponent>]
    let Bfs() =
        React.useEffect(fun () ->
            mathJaxTypeset()
        , [||])
        let state, dispatch = React.useElmish(init, update, [| |])
        match state with
        | TuringMachine tm ->
            Html.div
              [ prop.className "full-size"
                prop.children
                  [ //Html.div
                    //  [ prop.className "full-size"
                    //    prop.style [ style.backgroundColor.aquaMarine ]
                    //    prop.children
                    //      [ let drawMathOnCanvas (ctx : CanvasRenderingContext2D) (x: float) (y: float) =
                    //            let mathOutput = document.getElementById("x") :?> HTMLElement

                    //            if not (isNull mathOutput) then
                    //                // Create a temporary canvas to capture MathJax-rendered content as an image
                    //                let tempCanvas = document.createElement("canvas") :?> HTMLCanvasElement
                    //                tempCanvas.width <- mathOutput.offsetWidth
                    //                tempCanvas.height <- mathOutput.offsetHeight

                    //                // Get the 2D context of the temporary canvas
                    //                let tempCtx = tempCanvas.getContext("2d") :?> CanvasRenderingContext2D

                    //                // You cannot directly use mathOutput as an image; you'll need to render it somehow, for example:
                    //                // We could either draw the rendered text manually or use some rendering approach like svg2canvas, etc.

                    //                // Convert the temporary canvas to a data URL (image)
                    //                let img = document.createElement("img") :?> HTMLImageElement
                    //                img.src <- tempCanvas.toDataURL()

                    //                // Wait until the image is fully loaded
                    //                img.onload <- fun _ ->
                    //                    // Draw the image onto the original canvas
                    //                    ctx.drawImage(U3.Case1 img, x, y)
                    //        drawingcanvas {
                    //            Redraw = DrawFunction (fun ctx ->
                    //                ctx.canvas.width <- 400.0
                    //                ctx.canvas.height <- 400.0
                    //                ctx.translate(200.0, 200.0)
                    //                ctx.lineWidth <- 3.0
                    //                ctx.beginPath()
                    //                let radius = 100.
                    //                ctx.arc (0.0, 0.0, radius, 0.0, (2.0 * Math.PI), false)
                    //                ctx.stroke()
                    //                ctx.font <- "30px Arial"
                    //                let outerRadius = radius + 20.
                    //                let startX = 0.
                    //                let startY = float -outerRadius
                    //                let n = 10
                    //                for i in 0..n-1 do
                    //                    let theta = 2.*Math.PI / (float n) * float i
                    //                    let x = startX * Math.Cos(theta) - startY*Math.Sin(theta)
                    //                    let y = startX * Math.Sin(theta) + startY*Math.Cos(theta)
                    //                    if i = 3 then
                    //                        let x = startX * Math.Cos(theta) + float radius*Math.Sin(theta)
                    //                        let y = startX * Math.Sin(theta) - radius*Math.Cos(theta)
                    //                        ctx.beginPath()
                    //                        ctx.moveTo(0.0, 0.0)
                    //                        ctx.lineTo(x, y)
                    //                    ctx.textBaseline <- "middle"
                    //                    ctx.textAlign <- "center"
                    //                    //let mathOutput = document.getElementById("x")
                    //                    //let mathJaxSvg = mathOutput.querySelector("svg") :?> HTMLElement

                    //                    //let svgElement = mathOutput.querySelector("svg") :?> HTMLElement
                    //                    //if not <| isNull svgElement && svgElement.tagName.ToLower() = "svg" then
                    //                    //    // Serialize the SVG element to a string
                    //                    //    let svgData = JS.eval<string>("new XMLSerializer().serializeToString(arguments[0]);", svgElement)
                    //                    //    let svgBlob = Blob.Create([| U2.Case1 svgData |], BlobPropertyBag(Type = "image/svg+xml;charset=utf-8"))
                    //                    //    let url = URL.createObjectURL(svgBlob)

                    //                    //    let img = document.createElement("img") :?> HTMLImageElement
                    //                    //    img.src <- url
                    //                    //    let tempCanvas = document.createElement("canvas") :?> HTMLCanvasElement
                    //                    //    tempCanvas?width <- mathOutput.offsetWidth
                    //                    //    tempCanvas?height <- mathOutput.offsetHeight

                    //                    //    // Draw the MathJax-rendered content on the temporary canvas
                    //                    //    let tempCtx = tempCanvas?getContext("2d")
                    //                    //    tempCtx?drawImage(mathOutput, 0.0, 0.0)

                    //                    //    // Convert the temporary canvas to a data URL (image)
                    //                    //    let img = document.createElement("img") :?> HTMLImageElement
                    //                    //    img.src <- tempCanvas.toDataURL()

                    //                    //    img?onload <- fun _ ->
                    //                    //        ctx.drawImage(U3.Case1 img, x, y)
                    //                    //else
                    //                    //    window.alert "null"
                    //                ctx.stroke()
                    //            )
                    //            Props = []
                    //        } :?> ReactElement
                    //      ]
                    //  ]

                    text (string tm.BandZustand)
                    Html.div
                      [ for i in 1..1 do
                         yield
                          try
                              let startPos = Math.Min(tm.SchreibLesekopfPosition - 1, (tm.BandZustand |> List.findIndex(fun x -> x <> 'B')) - 1)
                              let endPos = Math.Max(tm.SchreibLesekopfPosition + 1, (tm.BandZustand |> List.findIndexBack(fun x -> x <> 'B')) + 1)
                              Html.div
                                [
                                  for j in startPos.. endPos do
                                    if tm.SchreibLesekopfPosition = j then
                                        yield text (string @$"(q_{tm.Zustand})")
                                    yield text (string (tm.BandZustand[j]))
                                ]
                          with
                          | _ ->
                              text ""
                                
                      ]


                    Html.button
                      [ prop.text "Next"
                        prop.onClick (fun _ -> dispatch Next)
                      ]

                    Html.button
                      [ prop.text "Prev"
                        prop.onClick (fun _ -> dispatch Prev)
                      ]
                  ]
            ]
        | RegisterMachine rm ->
            Html.div
              [ Html.table
                  [ Html.tr
                      [ for i in 0..100 do
                          Html.td [ prop.text (string rm.Speicher[i] ) ]
                      ]
                  ]
                Html.table
                  [ for i in 0..rm.Program.Length - 1 do
                      Html.tr
                        [ Html.td
                            [ prop.style
                                [ if i = rm.Befehlszaehler - 1 then style.backgroundColor.lightBlue else style.backgroundColor.transparent ]
                              prop.text ($"{i + 1}. {rm.Program[i]}" )
                            ]
                        ]
                  ]
                Html.button
                  [ prop.text "Next"
                    prop.onClick (fun _ -> dispatch Next)
                  ]

                Html.button
                  [ prop.text "Prev"
                    prop.onClick (fun _ -> dispatch Prev)
                  ]
              ]