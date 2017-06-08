open System
open System.Drawing

open Hekate

module Color =

    /// Answers the distance between two colors
    let dist (color1 : Color) (color2 : Color) =
        let sq comp1 comp2 =
            ((float comp1) - (float comp2)) ** 2.0
        sqrt (
            (sq color1.R color2.R) +
            (sq color1.G color2.G) +
            (sq color1.B color2.B))

    /// Finds the average of the given colors.
    let average colors =
        let r, g, b =
            colors
                |> Seq.map (fun (color : Color) ->
                    int color.R, int color.G, int color.B)
                |> Seq.reduce (fun (r1, g1, b1) (r2, g2, b2) ->
                    r1 + r2, g1 + g2, b1 + b2)
        let nColors = colors |> Array.length
        let avg value =
            int (float value / float nColors)
        Color.FromArgb(avg r, avg g, avg b)

module Bitmap =

    /// Crops the given portion of the given image.
    let crop (rect : Rectangle) (bitmap : Bitmap) =
        let result = new Bitmap(rect.Width, rect.Height)
        use g = Graphics.FromImage(result)
        g.DrawImage(
            bitmap,
            Rectangle(0, 0, rect.Width, rect.Height),
            rect,
            GraphicsUnit.Pixel)
        result

    /// Finds the average color near the given location in the
    /// given bitmap.
    let sample x y (bitmap : Bitmap) =
        let delta = 5
        [|
            for x' = (x - delta) to (x + delta) do
                if x' >= 0 && x' < bitmap.Width then
                    for y' = (y - delta) to (y + delta) do
                        if y' >= 0 && y' < bitmap.Height then
                            yield bitmap.GetPixel(x', y')
        |] |> Color.average

module UndirectedGraph =

    /// Answers the keys of the nodes adjacent to the node with
    /// the given key in the given undirected graph.
    let getNeighbors nodeKey graph =
        assert(
            (graph |> Graph.Nodes.predecessors nodeKey) =
                (graph |> Graph.Nodes.successors nodeKey))
        match graph |> Graph.Nodes.predecessors nodeKey with
            | Some neighbors ->
                neighbors
                    |> Seq.map fst
                    |> Seq.toArray
            | None -> failwith "Unexpected"

    /// Creates undirected edges between the node with the given
    /// key and the neighbor nodes with the given keys.
    let createEdges nodeKey neighborKeys =
        [
            for neighborKey in neighborKeys do
                yield neighborKey, nodeKey, ()
                yield nodeKey, neighborKey, ()
        ]

/// Every node in a graph has a unique key.
type NodeKey = int

/// A color's palette position is its unique key (1-based).
type ColorKey = int

/// Every node in a Kami graph is labeled with a color. Edges are unlabeled.
type KamiGraph = Graph<NodeKey, ColorKey, unit>

module Kami2 =

    /// Functions used only to create a graph from an image.
    module private Init =

        /// Extracts the palette from the given Kami2 image.
        let getPalette nColors image =
            let paletteWidth = 384
            let paletteHeight = 106
            use paletteImage =
                image
                    |> Bitmap.crop
                        (Rectangle(
                            image.Width - paletteWidth,
                            image.Height - paletteHeight,
                            paletteWidth,
                            paletteHeight))
            [|
                yield Color.FromArgb(220, 220, 220)   // inactive background
                yield! Seq.init nColors
                    (fun iColor ->
                        let x = int ((float iColor + 0.5) * (float paletteWidth) / (float nColors))
                        let y = paletteHeight / 2
                        paletteImage |> Bitmap.sample x y)
            |]

        /// Extracts the tiles from the given Kami2 image.
        let getTiles palette image : ColorKey[,] =
            use tilesImage =
                image |> Bitmap.crop (Rectangle(0, 0, 640, 1029))
            let nCols = 10
            let nRows = 29
            Array2D.init nCols nRows
                (fun iCol iRow ->
                    let actualColor =
                        let x =
                            int ((float iCol + 0.5) * float tilesImage.Width / float nCols)
                        let y =
                            iRow * (tilesImage.Height - 1) / (nRows - 1)
                        tilesImage |> Bitmap.sample x y
                    let paletteColor =
                        palette
                            |> Seq.minBy (Color.dist actualColor)
                    palette
                        |> Seq.findIndex (fun color ->
                            color = paletteColor))

        /// Answers triangular coordinates adjacent to the given
        /// coordinates. Example:
        ///
        ///    1,1           2,1
        ///      \           /
        ///       \         /
        ///       1,2 ---- 2,2
        ///       /         \
        ///      /           \
        ///    1,3           2,3
        ///
        let getAdjacentCoords x y =
            seq {
                yield x, y - 1
                yield x, y + 1
                if (x + y) % 2 = 0 then
                    yield x - 1, y
                else
                    yield x + 1, y
            }

        /// Merges all adjacent nodes of the same color in the given graph.
        let rec simplify (graph : KamiGraph) : KamiGraph =

                // is there a pair of adjancent nodes with the same color?
            let nodePairOpt =
                graph
                    |> Graph.Nodes.toList
                    |> Seq.tryPick (fun (nodeKey1, colorKey) ->
                        graph
                            |> UndirectedGraph.getNeighbors nodeKey1
                            |> Seq.tryPick (fun nodeKey2 ->
                                let _, colorKey2 =
                                    graph
                                        |> Graph.Nodes.find nodeKey2
                                if colorKey = colorKey2 then
                                    Some (nodeKey1, nodeKey2, colorKey)
                                else None))

                // merge them
            match nodePairOpt with
                | Some (nodeKeyKeep, nodeKeyRemove, colorKey) ->
                    let nodeKeyKeepNeighbors =
                        [
                            yield nodeKeyKeep
                            yield! graph
                                |> UndirectedGraph.getNeighbors nodeKeyKeep
                        ] |> Set.ofSeq
                    let edges =
                        graph
                            |> UndirectedGraph.getNeighbors nodeKeyRemove
                            |> Seq.where (fun nodeKey ->
                                assert(nodeKey <> nodeKeyRemove)
                                not <| nodeKeyKeepNeighbors.Contains(nodeKey))
                            |> UndirectedGraph.createEdges nodeKeyKeep
                    graph
                        |> Graph.Nodes.remove nodeKeyRemove
                        |> Graph.Edges.addMany edges
                        |> simplify
                | None -> graph

    /// Constructs a graph from the given Kami2 image.
    let createGraph image nColors =

            // read image
        let palette = image |> Init.getPalette nColors
        let tiles = image |> Init.getTiles palette

            // create a node for each tile
        let nodeTuples =
            tiles
                |> Array2D.mapi (fun x y colorKey ->
                    (x, y), colorKey)
                |> Seq.cast<(int * int) * ColorKey>
                |> Seq.where (fun (_, colorKey) ->   // ignore background
                    colorKey > 0)
                |> Seq.mapi (fun nodeKey (loc, colorKey) ->
                    nodeKey, colorKey, loc)
                |> Seq.toArray
        let nodeMap : Map<NodeKey, _> =
            nodeTuples
                |> Seq.map (fun (nodeKey, _, loc) ->
                    nodeKey, loc)
                |> Map.ofSeq
        let nodes =
            nodeTuples
                |> Seq.map (fun (nodeKey, colorKey, _) ->
                    nodeKey, colorKey)
                |> Seq.toList

            // create an edge for each pair of adjacent tiles
        let edges =
            let nodeMapInv =
                nodeTuples
                    |> Seq.map (fun (nodeKey, _, loc) ->
                        loc, nodeKey)
                    |> Map.ofSeq
            [
                for (KeyValue(nodeKey, (x, y))) in nodeMap do
                    for loc in Init.getAdjacentCoords x y do
                        match nodeMapInv |> Map.tryFind loc with
                            | Some adjNodeKey ->
                                yield nodeKey, adjNodeKey, ()
                            | None -> ()
            ]

            // create graph
        let graph =
            Graph.create nodes edges
                |> Init.simplify
        graph, nodeMap

    /// Fills the given node in the given graph with the given color.
    let fill nodeKey colorKey (graph : KamiGraph) : KamiGraph =

            // find nodes to be replaced
        let nodeKeys =
            graph
                |> UndirectedGraph.getNeighbors nodeKey
                |> Seq.map (fun neighborKey ->
                    graph |> Graph.Nodes.find neighborKey)
                |> Seq.where (fun (_, neighborColorKey) ->
                    neighborColorKey = colorKey)
                |> Seq.map fst
                |> Set.ofSeq
                |> Set.add nodeKey

            // find the merged node's neighbors
        let neighborKeys =
            nodeKeys
                |> Seq.collect (fun nodeKey ->
                    graph |> UndirectedGraph.getNeighbors nodeKey)
                |> Seq.distinct
                |> Seq.where (nodeKeys.Contains >> not)
                |> Seq.toArray
        assert(
            neighborKeys |>
                Seq.forall (fun neighborKey ->
                    let _, neighborColorKey =
                        graph |> Graph.Nodes.find neighborKey
                    neighborColorKey <> colorKey))

            // merge the same-color nodes together
        let edges =
            neighborKeys |> UndirectedGraph.createEdges nodeKey
        graph
            |> Graph.Nodes.removeMany (nodeKeys |> Seq.toList)
            |> Graph.Nodes.add (nodeKey, colorKey)
            |> Graph.Edges.addMany edges

    /// Attempts to solve the given graph in the given number of moves.
    let solve nMoves graph =

        let rec loop nMovesRemaining graph =
            assert(nMovesRemaining >= 0)
            assert(nMoves >= nMovesRemaining)

                // find remaining colors
            let nodes =
                graph
                    |> Graph.Nodes.toList
            let colorKeys =
                nodes
                    |> Seq.map snd
                    |> Seq.distinct
                    |> Seq.toArray

                // done if only one color left
            if colorKeys.Length <= 1 then
                Some []
            else
                    // still solvable? must have enough moves left to eliminate all colors but one
                let freedom = nMovesRemaining - colorKeys.Length + 1
                if freedom < 0 then None

                else
                    let legalMoves =
                        [|
                            for (nodeKey, curColorKey) in nodes do
                                for colorKey in colorKeys do
                                    if colorKey <> curColorKey then
                                        yield nodeKey, colorKey
                        |]
                    legalMoves
                        |> Array.Parallel.map (fun (nodeKey, colorKey) ->
                            let graph' =
                                graph |> fill nodeKey colorKey
                            (nodeKey, colorKey), graph')
                        |> Array.sortBy (fun (_, graph') ->
                            graph' |> Graph.Nodes.count)
                        |> Seq.mapi (fun iMove (move, graph') ->
                            iMove, move, graph')
                        |> Seq.tryPick (fun (iMove, move, graph') ->
                            let level = nMoves - nMovesRemaining
                            if level <= 1 && freedom >= 2 then
                                printfn "%sLevel %d: %4.1f%% complete"
                                    (String(' ', 3 * level))
                                    level
                                    (100.0 * (float iMove) / (float legalMoves.Length))
                            graph'
                                |> loop (nMovesRemaining - 1)
                                |> Option.map (fun moveList ->
                                    move :: moveList))

        graph |> loop nMoves

[<EntryPoint>]
let main argv =

        // construct graph from image
    use image = new Bitmap(argv.[0])
    let nColors = argv.[1] |> Int32.Parse
    let graph, nodeMap = Kami2.createGraph image nColors

        // solve graph
    let nMoves = argv.[2] |> Int32.Parse
    let dtStart = DateTime.Now
    match graph |> Kami2.solve nMoves with
        | Some moves ->
            printfn ""
            printfn "Solution:"
            for (nodeKey, colorKey) in moves do
                printfn
                    "   at %A put color %A"
                    nodeMap.[nodeKey]
                    colorKey
        | None ->
            printfn ""
            printfn "No solution"
    printfn ""
    printfn "%A" (DateTime.Now - dtStart)

    0
