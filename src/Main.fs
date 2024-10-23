module Main

open Feliz
open App
open Browser.Dom

let root = ReactDOM.createRoot(document.getElementById "bfs-app")
//root.render(Bfs.TuringMachine())
root.render(Bfs.Bfs())