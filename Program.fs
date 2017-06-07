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

    /// Answers the indices of the nodes adjacent to the node
    /// with the given index in the given undirected graph.
    let getNeighbors iNode graph =
        assert(
            (graph |> Graph.Nodes.predecessors iNode) =
                (graph |> Graph.Nodes.successors iNode))
        match graph |> Graph.Nodes.predecessors iNode with
            | Some neighbors ->
                neighbors
                    |> Seq.map fst
                    |> Seq.toArray
            | None -> failwith "Unexpected"

    /// Creates undirected edges between the node with the given
    /// index and the neighbor nodes with the given indexes.
    let createEdges iNode iNeighbors =
        [
            for iNeighbor in iNeighbors do
                yield iNeighbor, iNode, ()
                yield iNode, iNeighbor, ()
        ]

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
        let getTiles palette image =
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
        let rec simplify graph =

                // is there a pair of adjancent nodes with the same color?
            let nodePairOpt =
                graph
                    |> Graph.Nodes.toList
                    |> Seq.tryPick (fun (iNode1, iColor1) ->
                        graph
                            |> UndirectedGraph.getNeighbors iNode1
                            |> Seq.tryPick (fun iNode2 ->
                                let _, iColor2 =
                                    graph
                                        |> Graph.Nodes.find iNode2
                                if iColor1 = iColor2 then
                                    Some (iNode1, iNode2, iColor1)
                                else None))

                // merge them
            match nodePairOpt with
                | Some (iNodeKeep, iNodeRemove, iColor) ->
                    let iNodeKeepNeighbors =
                        [
                            yield iNodeKeep
                            yield! graph
                                |> UndirectedGraph.getNeighbors iNodeKeep
                        ] |> Set.ofSeq
                    let edges =
                        graph
                            |> UndirectedGraph.getNeighbors iNodeRemove
                            |> Seq.where (fun iNode ->
                                assert(iNode <> iNodeRemove)
                                not <| iNodeKeepNeighbors.Contains(iNode))
                            |> UndirectedGraph.createEdges iNodeKeep
                    graph
                        |> Graph.Nodes.remove iNodeRemove
                        |> Graph.Edges.addMany edges
                        |> simplify
                | None -> graph

    /// Constructs a graph from the given Kami2 image.
    let createGraph image nColors =

            // read image
        let palette = image |> Init.getPalette nColors
        let tiles = image |> Init.getTiles palette

            // create a node for each tile
        let nodes =
            tiles
                |> Array2D.mapi (fun x y iColor ->
                    (x, y), iColor)
                |> Seq.cast<(int * int) * int>
                |> Seq.where (fun (iNode, iColor) ->   // ignore background
                    iColor > 0)
                |> List.ofSeq
        let iNodes =
            nodes
                |> Seq.map fst
                |> Set.ofSeq

            // create an edge for each pair of adjacent tiles
        let edges =
            [
                for x, y in iNodes do
                    for iNode in Init.getAdjacentCoords x y do
                        if iNodes.Contains(iNode) then
                            yield (x, y), iNode, ()
            ]

            // create graph
        Graph.create nodes edges
            |> Init.simplify

    /// Fills the given node in the given graph with the given color.
    let fill iNode iColor graph =

            // find nodes to be replaced
        let iNodes =
            graph
                |> UndirectedGraph.getNeighbors iNode
                |> Seq.map (fun iNeighbor ->
                    graph |> Graph.Nodes.find iNeighbor)
                |> Seq.where (fun (_, iNeighborColor) ->
                    iNeighborColor = iColor)
                |> Seq.map fst
                |> Set.ofSeq
                |> Set.add iNode

            // find the merged node's neighbors
        let iNeighbors =
            iNodes
                |> Seq.collect (fun iNode ->
                    graph |> UndirectedGraph.getNeighbors iNode)
                |> Seq.distinct
                |> Seq.where (iNodes.Contains >> not)
                |> Seq.toArray
        assert(
            iNeighbors |>
                Seq.forall (fun iNeighbor ->
                    let _, iNeighborColor =
                        graph |> Graph.Nodes.find iNeighbor
                    iNeighborColor <> iColor))

            // merge the same-color nodes together
        let edges =
            iNeighbors |> UndirectedGraph.createEdges iNode
        graph
            |> Graph.Nodes.removeMany (iNodes |> Seq.toList)
            |> Graph.Nodes.add (iNode, iColor)
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
            let iColors =
                nodes
                    |> Seq.map snd
                    |> Seq.distinct
                    |> Seq.toArray

                // done if only one color left
            if iColors.Length <= 1 then
                Some []
            else
                    // still solvable? must have enough moves left to eliminate all colors but one
                let freedom = nMovesRemaining - iColors.Length + 1
                if freedom < 0 then None

                else
                    let legalMoves =
                        [|
                            for (iNode, iCurColor) in nodes do
                                for iColor in iColors do
                                    if iColor <> iCurColor then
                                        yield iNode, iColor
                        |]
                    legalMoves
                        |> Array.Parallel.map (fun (iNode, iColor) ->
                            let graph' =
                                graph |> fill iNode iColor
                            (iNode, iColor), graph')
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
    let graph = Kami2.createGraph image nColors

        // solve graph
    let nMoves = argv.[2] |> Int32.Parse
    let dtStart = DateTime.Now
    match graph |> Kami2.solve nMoves with
        | Some moves ->
            printfn ""
            printfn "Solution:"
            for (iNode, iColor) in moves do
                printfn "   at %A put color %A" iNode iColor
        | None ->
            printfn ""
            printfn "No solution"
    printfn ""
    printfn "%A" (DateTime.Now - dtStart)

    0
