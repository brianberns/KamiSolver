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
        let den =
            colors |> Array.length |> float
        let avg value =
            int (float value / den)
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
        let delta = 10
        [|
            for x' = (x - delta) to (x + delta) do
                if x' >= 0 && x' < bitmap.Width then
                    for y' = (y - delta) to (y + delta) do
                        if y' >= 0 && y' < bitmap.Height then
                            yield bitmap.GetPixel(x', y')
        |] |> Color.average

module Kami2 =

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
                assert(iNeighbor <> iNode)
                yield iNeighbor, iNode, ()
                yield iNode, iNeighbor, ()
        ]

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
            Array.init nColors
                (fun iColor ->
                    let x = int ((float iColor + 0.5) * (float paletteWidth) / (float nColors))
                    let y = paletteHeight / 2
                    paletteImage |> Bitmap.sample x y)

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

        /// Answers triangular coordinates adjacent to the given coordinates
        /// within the given dimensions. Example:
        ///
        ///    1,1           2,1
        ///      \           /
        ///       \         /
        ///       1,2 ---- 2,2
        ///       /         \
        ///      /           \
        ///    1,3           2,3
        ///
        let getAdjacentCoords x y width height =
            seq {
                if y > 0 then
                    yield x, y - 1
                if y < height - 1 then
                    yield x, y + 1
                if (x + y) % 2 = 0 then
                    if x > 0 then
                        yield x - 1, y
                else
                    if x < width - 1 then
                        yield x + 1, y
            }

        /// Merges adjacent nodes of the same color in the given graph.
        let rec simplify graph =

                // is there a pair of adjancent nodes with the same color?
            let nodePairOpt =
                graph
                    |> Graph.Nodes.toList
                    |> Seq.tryPick (fun (iNode1, iColor1) ->
                        graph
                            |> getNeighbors iNode1
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
                            yield! graph |> getNeighbors iNodeKeep
                        ] |> Set.ofSeq
                    let edges =
                        graph
                            |> getNeighbors iNodeRemove
                            |> Seq.where (fun iNode ->
                                assert(iNode <> iNodeRemove)
                                not <| iNodeKeepNeighbors.Contains(iNode))
                            |> createEdges iNodeKeep
                    graph
                        |> Graph.Nodes.remove iNodeRemove
                        |> Graph.Edges.addMany edges
                        |> simplify
                | None -> graph

    /// Constructs a graph from the given Kami2 image.
    let createGraph image nColors =

        let palette = image |> Init.getPalette nColors
        let tiles = image |> Init.getTiles palette

        let nodes =
            tiles
                |> Array2D.mapi (fun x y iColor ->
                    (x, y), iColor)
        let nodes =
            nodes
                |> Seq.cast<(int * int) * int>
                |> List.ofSeq
        let edges =
            let width = tiles.GetLength(0)
            let height = tiles.GetLength(1)
            [
                for x = 0 to width - 1 do
                    for y = 0 to height - 1 do
                        for (x', y') in Init.getAdjacentCoords x y width height do
                            yield (x, y), (x', y'), ()
            ]
        Graph.create nodes edges
            |> Init.simplify

    /// Fills the given node in the given graph with the given color.
    let fill iNode iColor graph =

            // find nodes to be replaced
        let iNodes =
            graph
                |> getNeighbors iNode
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
                    graph |> getNeighbors iNode)
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
            iNeighbors |> createEdges iNode
        graph
            |> Graph.Nodes.removeMany (iNodes |> Seq.toList)
            |> Graph.Nodes.add (iNode, iColor)
            |> Graph.Edges.addMany edges

    /// Attempts to solve the given graph in the given number of moves.
    let rec solve nMoves graph =
        assert(nMoves >= 0)
        if graph |> Graph.Nodes.count <= 1 then
            Some []
        else
            let nodes =
                graph
                    |> Graph.Nodes.toList
            let iColors =
                nodes
                    |> Seq.map snd
                    |> Seq.distinct
                    |> Seq.toArray
            if iColors.Length > nMoves + 1 then   // still solvable?
                None
            else
                let legalMovePairs =
                    [|
                        for (iNode, iExistingColor) in nodes do
                            for iColor in iColors do
                                if iColor <> iExistingColor then
                                    yield iNode, iColor
                    |]
                        |> Seq.map (fun (iNode, iColor) ->
                            let graph' =
                                graph |> fill iNode iColor
                            (iNode, iColor), graph')
                        |> Seq.sortBy (fun (_, graph') ->
                            graph' |> Graph.Nodes.count)
                        |> Seq.toArray
                legalMovePairs
                    |> Seq.tryPick (fun ((iNode, iColor), graph') ->
                        graph'
                            |> solve (nMoves - 1)
                            |> Option.map (fun moveList ->
                                (iNode, iColor) :: moveList))

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
            for move in moves do
                printfn "%A" move
        | None -> printfn "No solution"
    printfn "%A" (DateTime.Now - dtStart)

    0
