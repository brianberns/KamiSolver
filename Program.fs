open System
open System.Drawing

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

type Graph<'label> =
    {
        NodeMap : Map<int, 'label>
        Edges : bool[,]
        InTransaction : bool
        NextNodeKey : int
        MaxNodeKeys : int
    }

type Node<'label> = int * 'label

type Edge = ValueTuple<int, int>

module Graph =

    let create<'label> maxNodeKeys =
        {
            NodeMap = Map.empty<int, 'label>
            Edges =
                Array2D.init maxNodeKeys maxNodeKeys (fun _ _ ->
                    false)
            InTransaction = false
            NextNodeKey = 0
            MaxNodeKeys = maxNodeKeys
        }

    let nodeCount graph =
        graph.NodeMap.Count

    let getNodes graph : seq<Node<_>> =
        graph.NodeMap
            |> Map.toSeq

    let private getNodeKeys graph =
        graph
            |> getNodes
            |> Seq.map fst

    let getEdges graph : seq<Edge> =
        let nodeKeys = graph |> getNodeKeys
        seq {
            for i in nodeKeys do
                for j in nodeKeys do
                    if graph.Edges.[i, j] then
                        yield ValueTuple<_, _>(i, j)
        }

    let getLabel nodeKey graph =
        graph.NodeMap.[nodeKey]

    let getNeighbors nodeKey graph =
        let slice = graph.Edges.[nodeKey, *]
        graph
            |> getNodeKeys
            |> Seq.where (fun nodeKey -> slice.[nodeKey])

    let getNextNodeKey graph =
        let graph' =
            {
                graph with
                    NextNodeKey = graph.NextNodeKey + 1
            }
        graph.NextNodeKey, graph'

    let addNode nodeKey label graph =
        assert(nodeKey >= 0)
        assert(nodeKey < graph.MaxNodeKeys)
        assert(graph.NodeMap.ContainsKey(nodeKey) |> not)
        {
            graph with
                NodeMap =
                    graph.NodeMap |> Map.add nodeKey label
        }

    let private getWritableEdges graph =
        if graph.InTransaction then graph.Edges
        else graph.Edges |> Array2D.copy

    let beginTransaction graph =
        {
            graph with
                Edges = graph |> getWritableEdges
                InTransaction = true
        }

    let endTransaction graph =
        {
            graph with
                InTransaction = false
        }

    let removeManyNodes nodeKeys graph =
        {
            graph with
                NodeMap =
                    (graph.NodeMap, nodeKeys)
                        ||> Seq.fold (fun nodeMap nodeKey ->
                            nodeMap |> Map.remove nodeKey)
                Edges =
                    let edges = graph |> getWritableEdges
                    for nodeKey in nodeKeys do
                        for i = 0 to graph.MaxNodeKeys - 1 do
                            edges.[nodeKey, i] <- false
                            edges.[i, nodeKey] <- false
                    edges
        }

    let removeNode nodeKey graph =
        graph |> removeManyNodes [ nodeKey ]

    let addManyEdges (neighborKeyPairs : seq<int * seq<int>>) graph =
        {
            graph with
                Edges =
                    let edges = graph |> getWritableEdges
                    for nodeKey, neighborKeys in neighborKeyPairs do
                        assert(graph.NodeMap |> Map.containsKey(nodeKey))
                        assert(neighborKeys |> Seq.forall (fun key -> graph.NodeMap |> Map.containsKey key))
                        for neighborKey in neighborKeys do
                            edges.[nodeKey, neighborKey] <- true
                            edges.[neighborKey, nodeKey] <- true
                    edges
        }

    /// Adds edges between the given node and the neighbor nodes with the given keys.
    let addEdges nodeKey neighborKeys graph =
        graph |> addManyEdges [ nodeKey, neighborKeys ]

    let compress graph =
        let newGraph =
            create graph.NodeMap.Count
        let newGraph, keyPairs =
            ((newGraph, List.empty), graph |> getNodes)
                ||> Seq.fold (fun (newGraph, keyPairs) (oldNodeKey, label) ->
                    let newNodeKey, newGraph = newGraph |> getNextNodeKey
                    let newGraph = newGraph |> addNode newNodeKey label
                    let keyPairs = (oldNodeKey, newNodeKey) :: keyPairs
                    newGraph, keyPairs)
        let keyMap = keyPairs |> Map.ofSeq
        let newGraph =
            let newNeighborKeyPairs =
                graph
                    |> getEdges
                    |> Seq.groupBy (fun edge -> edge.Item1)
                    |> Seq.map (fun (oldNodeKey, group) ->
                        let newNodeKey = keyMap.[oldNodeKey]
                        let newNeighborKeys =
                            group
                                |> Seq.map (fun edge ->
                                    keyMap.[edge.Item2])
                                |> Seq.where (fun newNeighborKey ->
                                    newNeighborKey > newNodeKey)
                        newNodeKey, newNeighborKeys)
            newGraph |> addManyEdges newNeighborKeyPairs
        newGraph, keyMap

    /// https://www.wikiwand.com/en/Floyd%E2%80%93Warshall_algorithm
    let getDistances graph =
        let nNodes = graph |> nodeCount
        let result =
            Array2D.init nNodes nNodes (fun i j ->
                if i = j then 0
                else 2 * nNodes)   // larger than max possible distance between two nodes
        let nodeMap =
            graph
                |> getNodes
                |> Seq.mapi (fun i (key, _) -> key, i)
                |> Map.ofSeq
        for edge in graph |> getEdges do
            result.[nodeMap.[edge.Item1], nodeMap.[edge.Item2]] <- 1
        for k = 0 to nNodes - 1 do
            for i = 0 to nNodes - 1 do
                for j = 0 to nNodes - 1 do
                    let sum = result.[i, k] + result.[k, j]
                    if result.[i, j] > sum then
                        result.[i, j] <- sum
        result, nodeMap

/// A color's palette position is its unique key (1-based).
type ColorKey = int

/// Every node in a Kami graph is labeled with a color.
type KamiGraph = Graph<ColorKey>

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

        /// Answers triangular coordinates adjacent to the given coordinates.
        /// Example:
        ///
        ///    1,1           2,1
        ///      \           /
        ///       \         /
        ///       1,2 ---- 2,2
        ///       /         \
        ///      /           \
        ///    1,3           2,3
        ///
        let getAdjacentLocations x y =
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
                    |> Graph.getNodes
                    |> Seq.tryPick (fun (nodeKey1, colorKey1) ->
                        graph
                            |> Graph.getNeighbors nodeKey1
                            |> Seq.tryPick (fun nodeKey2 ->
                                let colorKey2 =
                                    graph
                                        |> Graph.getLabel nodeKey2
                                if colorKey1 = colorKey2 then
                                    Some (nodeKey1, nodeKey2, colorKey1)
                                else None))

                // merge them
            match nodePairOpt with
                | Some (nodeKeyKeep, nodeKeyRemove, colorKey) ->

                        // find nodes that the kept node is already attached to
                    let nodeKeyKeepNeighbors =
                        [
                            yield nodeKeyKeep
                            yield! graph
                                |> Graph.getNeighbors nodeKeyKeep
                        ] |> Set.ofSeq

                        // do we need to attach the kept node to any of the removed node's neighbors?
                    let newNeighborKeys =
                        graph
                            |> Graph.getNeighbors nodeKeyRemove
                            |> Seq.where (fun nodeKey ->
                                not <| nodeKeyKeepNeighbors.Contains(nodeKey))
                    graph
                        |> Graph.removeNode nodeKeyRemove
                        |> Graph.addEdges nodeKeyKeep newNeighborKeys
                        |> simplify
                | None -> graph

    /// Constructs a graph from the given Kami2 image.
    let createGraph image nColors =

            // read image
        let palette = image |> Init.getPalette nColors
        let tiles = image |> Init.getTiles palette

            // create a node for each tile
        let locColors =
            tiles
                |> Array2D.mapi (fun x y colorKey ->
                    (x, y), colorKey)
                |> Seq.cast<(int * int) * ColorKey>
                |> Seq.where (fun (_, colorKey) ->   // ignore background
                    colorKey > 0)
                |> Seq.toArray
        let graph =
            Graph.create<ColorKey> tiles.Length
        let graph, keyLocs =
            ((graph, List.empty), locColors)
                ||> Seq.fold (fun (graph, keyLocs) (loc, colorKey) ->
                    let nodeKey, graph =
                        graph |> Graph.getNextNodeKey
                    let graph =
                        graph |> Graph.addNode nodeKey colorKey
                    let keyLocs =
                        (nodeKey, loc) :: keyLocs
                    graph, keyLocs)
        let keyLocMap =
            keyLocs |> Map.ofSeq

            // create an edge for each pair of adjacent tiles
        let graph =
            let locKeyMap =
                keyLocs
                    |> Seq.map (fun (nodeKey, loc) -> loc, nodeKey)
                    |> Map.ofSeq
            let adjKeyPairs =
                keyLocs
                    |> Seq.map (fun (nodeKey, (x, y)) ->
                        let adjNodeKeys =
                            Init.getAdjacentLocations x y
                                |> Seq.choose (fun adjLoc ->
                                    locKeyMap |> Map.tryFind adjLoc)
                        nodeKey, adjNodeKeys)
            graph |> Graph.addManyEdges adjKeyPairs

        let graph, keyMap =
            graph
                |> Init.simplify
                |> Graph.compress
        let keyLocMap =
            keyLocMap
                |> Map.toSeq
                |> Seq.choose (fun (oldNodeKey, loc) ->
                    keyMap
                        |> Map.tryFind oldNodeKey
                        |> Option.map (fun newNodeKey ->
                            newNodeKey, loc))
                |> Map.ofSeq
        graph, keyLocMap

    /// Fills the given node in the given graph with the given color, which merges
    /// it with neighboring nodes of the same color.
    let fill nodeKey colorKey (graph : KamiGraph) : (KamiGraph * int (*num nodes removed*)) =

            // determine nodes to be merged
        let nodeKeys =
            graph
                |> Graph.getNeighbors nodeKey
                |> Seq.map (fun neighborKey ->
                    let label = graph |> Graph.getLabel neighborKey
                    neighborKey, label)
                |> Seq.where (fun (_, neighborColorKey) ->
                    neighborColorKey = colorKey)
                |> Seq.map fst
                |> Set.ofSeq
                |> Set.add nodeKey

            // find the merged nodes' neighbors
        let neighborKeys =
            nodeKeys
                |> Seq.collect (fun nodeKey ->
                    graph |> Graph.getNeighbors nodeKey)
                |> Seq.distinct
                |> Seq.where (nodeKeys.Contains >> not)
                |> Seq.toArray
        assert(
            neighborKeys |>
                Seq.forall (fun neighborKey ->
                    let neighborColorKey =
                        graph |> Graph.getLabel neighborKey
                    neighborColorKey <> colorKey))

            // merge the same-color nodes together
        let graph =
            graph
                |> Graph.beginTransaction
                |> Graph.removeManyNodes (nodeKeys |> Seq.toList)
                |> Graph.addNode nodeKey colorKey
                |> Graph.addEdges nodeKey neighborKeys
                |> Graph.endTransaction
        graph, nodeKeys.Count - 1

    /// Attempts to solve the given graph in the given number of moves.
    let solve nMoves nodeMap (graph : KamiGraph) =

        let priorityMap =
            let distances, nodeMap =
                graph |> Graph.getDistances
            graph
                |> Graph.getNodes
                |> Seq.map (fun (nodeKey, _) ->
                    let maxDist =
                        distances.[nodeMap.[nodeKey], *] |> Seq.max
                    let nNeighbors =
                        graph
                            |> Graph.getNeighbors nodeKey
                            |> Seq.length
                    nodeKey, maxDist, nNeighbors)
                |> Seq.sortBy (fun (_, maxDist, nNeighbors) ->
                    maxDist, -nNeighbors)
                |> Seq.mapi (fun i (nodeKey, _, _) -> nodeKey, i)
                |> Map.ofSeq

        let rec loop nMovesRemaining (graph : KamiGraph) =
            assert(nMovesRemaining >= 0)
            assert(nMoves >= nMovesRemaining)

                // find remaining colors
            let nodes =
                graph
                    |> Graph.getNodes
                    |> Seq.toArray
            let colorKeys =
                nodes
                    |> Seq.map snd
                    |> Seq.distinct
                    |> Seq.sort
                    |> Seq.toArray

                // done if only one color left
            if colorKeys.Length <= 1 then
                Some []
            else
                    // still solvable? must have enough moves left to eliminate all colors but one
                let freedom = nMovesRemaining - colorKeys.Length + 1
                if freedom < 0 then None
                else
                    nodes
                        |> Seq.sortBy (fun (nodeKey, _) -> priorityMap.[nodeKey])
                        |> Seq.mapi (fun iNode node -> iNode, node)
                        |> Seq.tryPick (fun (iNode, (nodeKey, curColorKey)) ->

                            let level = nMoves - nMovesRemaining

                            let moves =
                                colorKeys
                                    |> Seq.where (fun newColorKey ->
                                        newColorKey <> curColorKey)
                                    |> Seq.map (fun newColorKey ->
                                        nodeKey, newColorKey)
                                    |> Seq.toArray

                            moves
                                |> Array.Parallel.mapi (fun iMove move ->
                                    let nodeKey, newColorKey = move
                                    let graph', delta =
                                        graph
                                            |> fill nodeKey newColorKey
                                    iMove, move, graph', delta)
                                |> Seq.tryPick (fun (iMove, move, graph', delta) ->  

                                    if level <= 1 && freedom >= 2 then
                                        let nMoves =
                                            nodes.Length * (colorKeys.Length - 1)
                                        printfn "%sLevel %d: %4.1f%% complete, node %A, color %A"
                                            (String(' ', 3 * level))
                                            level
                                            (100.0 * float ((iNode * moves.Length) + iMove) / float nMoves)
                                            (nodeMap |> Map.find nodeKey)
                                            (snd move)

                                    if delta <= 0 then
                                        assert(delta = 0)
                                        None
                                    else
                                        graph'
                                            |> loop (nMovesRemaining - 1)
                                            |> Option.map (fun moveList ->
                                                move :: moveList)))

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
    match graph |> Kami2.solve nMoves nodeMap with
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
