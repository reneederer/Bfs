namespace App

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

module Bfs =

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
          Blank : char
          Program : Map<(Zustand * BandZeichen), (Zustand * BandZeichen * SchreibLesekopfBewegung)>
          Zustandsmenge : int list
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
                    s.ToLower()
                      .Replace(",", "")
                      .Replace("-", "")
                      .Replace("_", "")
                      .Replace("  ", " ")
                      .Trim()
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
                        let m = Regex.Match(s, "(if|ifgoto)\s+(\d+)\s+(\w+)\s+(\d+)\s+(\d+);?$")
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
        let blank = '-'
        let eingabemenge = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890 ".ToCharArray() |> List.ofArray
        (TuringMachine
            { BandZustand = List.init 2000 (fun i -> blank)
              SchreibLesekopfPosition = 1000
              Eingabemenge = ['0'; '1']
              Bandeingabemenge = ['0'; '1'; 'B'; 'X'; 'Y']
              Blank = blank
              Zustandsmenge = [0;1;2;3;4;5]
              Program =
                [ (0, '0'), (1, 'X', SchreibLesekopfBewegung.R)
                  (1, '0'), (1, '0', SchreibLesekopfBewegung.R)
                  (2, '0'), (4, '0', SchreibLesekopfBewegung.L)
                  (4, '0'), (4, '0', SchreibLesekopfBewegung.L)

                  (1, '1'), (2, 'Y', SchreibLesekopfBewegung.L)

                  (3, 'B'), (5, 'Y', SchreibLesekopfBewegung.R)

                  (2, 'X'), (3, 'X', SchreibLesekopfBewegung.R)
                  (4, 'X'), (0, 'X', SchreibLesekopfBewegung.R)

                  (1, 'Y'), (1, 'X', SchreibLesekopfBewegung.R)
                  (2, 'Y'), (2, 'X', SchreibLesekopfBewegung.L)
                  (3, 'Y'), (3, 'X', SchreibLesekopfBewegung.R)
                ]
                |> Map.ofList
            }, Cmd.none)
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
            printfn $"{json}"
            state, Cmd.none
        | TuringMachine tm, Prev -> state, Cmd.none
        | RegisterMachine rm, Prev -> state, Cmd.none
        | RegisterMachine rm, Next ->
            RegisterMachine (rm.Next()), Cmd.none

    [<ReactComponent>]
    let Bfs() =
        let state, dispatch = React.useElmish(init, update, [| |])
        match state with
        | TuringMachine tm ->
            Html.div
              [ prop.className "full-size"
                prop.children
                  [ Html.div
                      [ prop.className "full-size"
                        prop.style [ style.backgroundColor.aquaMarine ]
                        prop.children
                          [ drawingcanvas {
                                Redraw = DrawFunction (fun ctx ->
                                    ctx.canvas.width <- 400.0
                                    ctx.canvas.height <- 400.0
                                    ctx.translate(200.0, 200.0)
                                    ctx.lineWidth <- 3.0
                                    ctx.beginPath()
                                    let radius = 100.
                                    ctx.arc (0.0, 0.0, radius, 0.0, (2.0 * Math.PI), false)
                                    ctx.stroke()
                                    ctx.font <- "30px Arial"
                                    let outerRadius = radius + 20.
                                    let startX = 0.
                                    let startY = float -outerRadius
                                    let n = 10
                                    for i in 0..n-1 do
                                        let theta = 2.*Math.PI / (float n) * float i
                                        let x = startX * Math.Cos(theta) - startY*Math.Sin(theta)
                                        let y = startX * Math.Sin(theta) + startY*Math.Cos(theta)
                                        if i = 3 then
                                            let x = startX * Math.Cos(theta) + float radius*Math.Sin(theta)
                                            let y = startX * Math.Sin(theta) - radius*Math.Cos(theta)
                                            ctx.beginPath()
                                            ctx.moveTo(0.0, 0.0)
                                            ctx.lineTo(x, y)
                                        ctx.textBaseline <- "middle"
                                        ctx.textAlign <- "center"
                                        ctx.fillText($"{i}", x, y)
                                    ctx.stroke()
                                )
                                Props = []
                            } :?> ReactElement
                          ]
                      ]
                    Html.table
                      [ Html.tr
                          [ for i in 0..0 do
                              Html.td [ prop.text (string tm.Bandeingabemenge[i] ) ]
                          ]
                      ]
                    Html.table
                      [ for i in 0..1 do
                          Html.tr
                            [ Html.td
                                [ prop.style
                                    [ if i = 1 then style.backgroundColor.lightBlue else style.backgroundColor.transparent ]
                                  prop.text ($"{i + 1}. {1}" )
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