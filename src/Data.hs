-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)


module Data where
	import Letter
	import AlphabetCSP
	
	getGroupGens :: [[[Int]]] -> GroupGens
	getGroupGens = map (map (map Atom))
	
	classes6 :: IO [[GroupGens]]
	classes6 = do
		clf <- readFile "data6.txt"
		let cl :: [[[[[Atom]]]]] = map (map getGroupGens) (read clf)
		return cl

		
	results6 :: IO [(GroupGens, Bool)]
	results6 = do
		l <- readFile "all6.txt"
		let rs :: [([[[Atom]]], Bool)] = map (\(x, b) -> (getGroupGens x, b)) $ read l
		return rs
		
	results7 :: IO [(GroupGens, Bool)]
	results7 = do
		l <- readFile "all7.txt"
		let rs :: [([[[Atom]]], Bool)] = map (\(x, b) -> (getGroupGens x, b)) $ read l
		return rs
		
	results8 :: IO [(GroupGens, Bool)]
	results8 = do
		l <- readFile "all8.txt"
		let rs :: [([[[Atom]]], Bool)] = map (\(x, b) -> (getGroupGens x, b)) $ read l
		return rs


	s :: [[GroupGens]]
	s = [s1, s2, s3, s4, s5, s6, s7, s8]

	s1 :: [GroupGens]
	s1 = map getGroupGens [ [  ] ]

	s2 :: [GroupGens]
	s2 = map getGroupGens [ [ [[]] ], [ [[1,2]] ] ]

	s3 :: [GroupGens]
	s3 = map getGroupGens [ [  ], [ [[2,3]] ], [ [[1,2,3]] ], [ [[1,2,3]], [[2,3]] ] ]

	s4 :: [GroupGens]
	s4 = map getGroupGens [ [  ], [ [[1,3],[2,4]] ], [ [[3,4]] ], [ [[2,4,3]] ], [ [[1,4],[2,3]], [[1,3],[2,4]] ], 
	  [ [[3,4]], [[1,2],[3,4]] ], [ [[1,3,2,4]], [[1,2],[3,4]] ], [ [[3,4]], [[2,4,3]] ], 
	  [ [[1,4],[2,3]], [[1,3],[2,4]], [[3,4]] ], [ [[1,4],[2,3]], [[1,3],[2,4]], [[2,4,3]] ], 
	  [ [[1,4],[2,3]], [[1,3],[2,4]], [[2,4,3]], [[3,4]] ] ]
	  
	s5 :: [GroupGens]
	s5 = map getGroupGens [ [  ], [ [[4,5]] ], [ [[2,3],[4,5]] ], [ [[3,4,5]] ], [ [[2,3],[4,5]], [[2,4],[3,5]] ], 
	  [ [[2,3],[4,5]], [[2,4,3,5]] ], [ [[4,5]], [[2,3]] ], [ [[1,2,3,4,5]] ], 
	  [ [[3,4,5]], [[4,5]] ], [ [[3,4,5]], [[1,2],[4,5]] ], [ [[4,5]], [[1,2,3]] ], 
	  [ [[4,5]], [[2,3]], [[2,4],[3,5]] ], [ [[1,2,3,4,5]], [[2,5],[3,4]] ], 
	  [ [[2,3],[4,5]], [[2,4],[3,5]], [[3,4,5]] ], [ [[4,5]], [[1,2,3]], [[2,3]] ], 
	  [ [[1,2,3,4,5]], [[2,5],[3,4]], [[2,3,5,4]] ], 
	  [ [[2,3],[4,5]], [[2,4],[3,5]], [[3,4,5]], [[4,5]] ], [ [[1,2,3,4,5]], [[3,4,5]] ], 
	  [ [[1,2,3,4,5]], [[1,2]] ] ]


	s6 :: [GroupGens]
	s6 = map getGroupGens [ [  ], [ [[5,6]] ], [ [[1,2],[3,4],[5,6]] ], [ [[3,4],[5,6]] ], [ [[4,5,6]] ], 
	  [ [[1,2,3],[4,5,6]] ], [ [[3,4],[5,6]], [[1,2],[5,6]] ], [ [[3,4],[5,6]], [[3,5],[4,6]] ], 
	  [ [[3,4],[5,6]], [[1,2],[3,5,4,6]] ], [ [[3,4],[5,6]], [[1,2],[3,5],[4,6]] ], 
	  [ [[3,4],[5,6]], [[3,5,4,6]] ], [ [[5,6]], [[3,4]] ], [ [[5,6]], [[1,2],[3,4]] ], 
	  [ [[2,3,4,5,6]] ], [ [[1,2,3],[4,5,6]], [[1,4],[2,6],[3,5]] ], [ [[4,5,6]], [[5,6]] ], 
	  [ [[4,5,6]], [[2,3],[5,6]] ], [ [[1,2,3],[4,5,6]], [[2,3],[5,6]] ], 
	  [ [[1,2],[3,4],[5,6]], [[1,3,5],[2,4,6]] ], [ [[5,6]], [[2,3,4]] ], 
	  [ [[5,6]], [[1,2],[3,4]], [[1,3],[2,4]] ], [ [[5,6]], [[3,4]], [[1,2]] ], 
	  [ [[5,6]], [[3,4]], [[1,2],[3,5],[4,6]] ], [ [[5,6]], [[3,4]], [[3,5],[4,6]] ], 
	  [ [[3,4],[5,6]], [[3,5],[4,6]], [[1,2],[5,6]] ], 
	  [ [[3,4],[5,6]], [[3,5,4,6]], [[1,2],[5,6]] ], [ [[5,6]], [[1,2],[3,4]], [[1,3,2,4]] ], 
	  [ [[4,5,6]], [[1,2,3]] ], [ [[2,3,4,5,6]], [[3,6],[4,5]] ], 
	  [ [[3,4],[5,6]], [[1,2],[5,6]], [[1,3,5],[2,4,6]] ], 
	  [ [[3,4],[5,6]], [[3,5],[4,6]], [[4,5,6]] ], [ [[5,6]], [[2,3,4]], [[3,4]] ], 
	  [ [[1,2],[3,4],[5,6]], [[1,3,5],[2,4,6]], [[3,5],[4,6]] ], 
	  [ [[3,4]], [[5,6]], [[3,5],[4,6]], [[1,2]] ], [ [[4,5,6]], [[1,2,3]], [[2,3],[5,6]] ], 
	  [ [[4,5,6]], [[1,2,3]], [[1,4],[2,5],[3,6]] ], [ [[4,5,6]], [[5,6]], [[1,2,3]] ], 
	  [ [[2,3,4,5,6]], [[3,6],[4,5]], [[3,4,6,5]] ], 
	  [ [[5,6]], [[3,4]], [[1,2]], [[1,3,5],[2,4,6]] ], 
	  [ [[5,6]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]] ], 
	  [ [[3,4],[5,6]], [[3,5],[4,6]], [[4,5,6]], [[1,2],[5,6]] ], 
	  [ [[3,4],[5,6]], [[1,2],[5,6]], [[1,3,5],[2,4,6]], [[3,5],[4,6]] ], 
	  [ [[3,4],[5,6]], [[1,2],[5,6]], [[1,3,5],[2,4,6]], [[3,5,4,6]] ], 
	  [ [[3,4],[5,6]], [[3,5],[4,6]], [[4,5,6]], [[5,6]] ], 
	  [ [[4,5,6]], [[5,6]], [[1,2,3]], [[2,3]] ], 
	  [ [[4,5,6]], [[1,2,3]], [[2,3],[5,6]], [[1,4],[2,5],[3,6]] ], 
	  [ [[4,5,6]], [[1,2,3]], [[2,3],[5,6]], [[1,4],[2,5,3,6]] ], 
	  [ [[5,6]], [[3,4]], [[1,2]], [[1,4,5],[2,3,6]], [[3,5],[4,6]] ], 
	  [ [[5,6]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], [[3,4]] ], [ [[1,2,3,4,5]], [[3,4,5]] ],
	  [ [[1,2,3,4,6]], [[1,4],[5,6]] ], 
	  [ [[4,6,5]], [[4,5]], [[1,2,3]], [[2,3]], [[1,4],[2,5],[3,6]] ], 
	  [ [[1,5,4,3,2]], [[2,4,3]], [[4,5]] ], [ [[1,5,3,6,4]], [[1,6],[2,4]], [[3,4,6,5]] ], 
	  [ [[1,2,3,4,5]], [[4,5,6]] ], [ [[1,2,3,4,5,6]], [[1,2]] ] ]
	  
	s7 :: [GroupGens]
	s7 = map getGroupGens [ [  ], [ [[6,7]] ], [ [[4,5],[6,7]] ], [ [[2,3],[4,5],[6,7]] ], [ [[5,6,7]] ], 
	  [ [[2,3,4],[5,6,7]] ], [ [[4,5],[6,7]], [[4,6],[5,7]] ], [ [[4,5],[6,7]], [[2,3],[6,7]] ], 
	  [ [[6,7]], [[4,5]] ], [ [[4,5],[6,7]], [[4,6,5,7]] ], [ [[4,5],[6,7]], [[2,3],[4,6,5,7]] ],
	  [ [[4,5],[6,7]], [[2,3],[4,6],[5,7]] ], [ [[6,7]], [[2,3],[4,5]] ], [ [[3,4,5,6,7]] ], 
	  [ [[5,6,7]], [[6,7]] ], [ [[5,6,7]], [[1,2],[3,4]] ], [ [[5,6,7]], [[1,2],[3,4],[6,7]] ], 
	  [ [[2,3,4],[5,6,7]], [[2,5],[3,7],[4,6]] ], [ [[5,6,7]], [[3,4],[6,7]] ], 
	  [ [[6,7]], [[3,4,5]] ], [ [[2,3],[4,5],[6,7]], [[2,4,6],[3,5,7]] ], 
	  [ [[2,3,4],[5,6,7]], [[3,4],[6,7]] ], [ [[1,2,3,4,5,6,7]] ], 
	  [ [[6,7]], [[2,3],[4,5]], [[2,4],[3,5]] ], [ [[6,7]], [[4,5]], [[2,3]] ], 
	  [ [[6,7]], [[4,5]], [[4,6],[5,7]] ], [ [[6,7]], [[2,3],[4,5]], [[2,4,3,5]] ], 
	  [ [[4,5],[6,7]], [[4,6,5,7]], [[2,3],[6,7]] ], [ [[6,7]], [[4,5]], [[2,3],[4,6],[5,7]] ], 
	  [ [[4,5],[6,7]], [[4,6],[5,7]], [[2,3],[6,7]] ], [ [[5,6,7]], [[2,3,4]] ], 
	  [ [[3,4,5,6,7]], [[1,2],[4,7],[5,6]] ], [ [[3,4,5,6,7]], [[4,7],[5,6]] ], 
	  [ [[6,7]], [[1,2,3,4,5]] ], [ [[4,5],[6,7]], [[4,6],[5,7]], [[5,6,7]] ], 
	  [ [[5,6,7]], [[1,2],[3,4]], [[1,3],[2,4]] ], 
	  [ [[4,5],[6,7]], [[4,6],[5,7]], [[1,2,3],[5,6,7]] ], [ [[6,7]], [[4,5]], [[1,2,3]] ], 
	  [ [[4,5],[6,7]], [[2,3],[6,7]], [[2,4,6],[3,5,7]] ], 
	  [ [[5,6,7]], [[3,4],[6,7]], [[1,2],[6,7]] ], 
	  [ [[5,6,7]], [[1,2],[3,4]], [[1,3],[2,4],[6,7]] ], 
	  [ [[5,6,7]], [[1,2],[3,4]], [[1,3,2,4],[6,7]] ], [ [[5,6,7]], [[6,7]], [[1,2],[3,4]] ], 
	  [ [[5,6,7]], [[1,2],[3,4]], [[1,3,2,4]] ], [ [[6,7]], [[3,4,5]], [[4,5]] ], 
	  [ [[6,7]], [[3,4,5]], [[1,2],[4,5]] ], 
	  [ [[2,3],[4,5],[6,7]], [[2,4,6],[3,5,7]], [[4,6],[5,7]] ], 
	  [ [[1,2,3,4,5,6,7]], [[2,7],[3,6],[4,5]] ], [ [[4,5]], [[6,7]], [[4,6],[5,7]], [[2,3]] ], 
	  [ [[5,6,7]], [[2,3,4]], [[3,4],[6,7]] ], [ [[5,6,7]], [[2,3,4]], [[2,5],[3,6],[4,7]] ], 
	  [ [[5,6,7]], [[6,7]], [[2,3,4]] ], [ [[3,4,5,6,7]], [[4,7],[5,6]], [[1,2],[4,5,7,6]] ], 
	  [ [[6,7]], [[1,2,3,4,5]], [[2,5],[3,4]] ], [ [[3,4,5,6,7]], [[4,7],[5,6]], [[4,5,7,6]] ], 
	  [ [[1,2,3,4,5,6,7]], [[2,3,5],[4,7,6]] ], 
	  [ [[4,5],[6,7]], [[4,6],[5,7]], [[5,6,7]], [[6,7]] ], 
	  [ [[5,6,7]], [[6,7]], [[1,2],[3,4]], [[1,3],[2,4]] ], [ [[6,7]], [[4,5]], [[1,2,3]], [[2,3]] ]
		, [ [[4,5]], [[6,7]], [[4,6],[5,7]], [[1,2,3]] ], 
	  [ [[5,6,7]], [[3,4],[6,7]], [[1,2],[6,7]], [[1,3],[2,4],[6,7]] ], 
	  [ [[6,7]], [[2,3],[4,5]], [[2,4],[3,5]], [[3,4,5]] ], 
	  [ [[4,5],[6,7]], [[2,3],[6,7]], [[2,4,6],[3,5,7]], [[4,6,5,7]] ], 
	  [ [[6,7]], [[4,5]], [[2,3]], [[2,4,6],[3,5,7]] ], 
	  [ [[6,7]], [[4,5]], [[1,2,3]], [[2,3],[4,6],[5,7]] ], 
	  [ [[5,6,7]], [[6,7]], [[1,2],[3,4]], [[1,3,2,4]] ], 
	  [ [[5,6,7]], [[3,4],[6,7]], [[1,2],[6,7]], [[1,3],[2,4]] ], 
	  [ [[4,5],[6,7]], [[4,6],[5,7]], [[5,6,7]], [[2,3],[6,7]] ], 
	  [ [[4,5],[6,7]], [[2,3],[6,7]], [[2,4,6],[3,5,7]], [[4,6],[5,7]] ], 
	  [ [[4,5],[6,7]], [[4,6],[5,7]], [[1,2,3],[5,6,7]], [[2,3],[6,7]] ], 
	  [ [[5,6,7]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]] ], 
	  [ [[5,6,7]], [[2,3,4]], [[3,4],[6,7]], [[2,5],[3,6],[4,7]] ], 
	  [ [[5,6,7]], [[6,7]], [[2,3,4]], [[3,4]] ], 
	  [ [[5,6,7]], [[2,3,4]], [[3,4],[6,7]], [[2,5],[3,6,4,7]] ], 
	  [ [[6,7]], [[1,2,3,4,5]], [[2,5],[3,4]], [[2,3,5,4]] ], 
	  [ [[1,2,3,4,5,6,7]], [[2,3,5],[4,7,6]], [[2,7],[3,6],[4,5]] ], 
	  [ [[6,7]], [[2,3],[4,5]], [[2,4],[3,5]], [[3,4,5]], [[4,5]] ], 
	  [ [[4,5]], [[6,7]], [[4,6],[5,7]], [[1,2,3]], [[2,3]] ], 
	  [ [[6,7]], [[4,5]], [[2,3]], [[2,5,6],[3,4,7]], [[4,6],[5,7]] ], 
	  [ [[1,2,3,4,5]], [[3,4,5]] ], [ [[1,2,3,4,6]], [[1,4],[5,6]] ], 
	  [ [[5,6,7]], [[6,7]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]] ], 
	  [ [[5,6,7]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], [[3,4]] ], 
	  [ [[5,6,7]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], [[3,4],[6,7]] ], 
	  [ [[5,7,6]], [[5,6]], [[2,4,3]], [[3,4]], [[2,5],[3,6],[4,7]] ], 
	  [ [[1,2,3,4,5]], [[3,4,5]], [[6,7]] ], [ [[1,2,3,4,5]], [[3,4,5]], [[4,5]] ], 
	  [ [[1,2,3,4,5]], [[3,4,5]], [[4,5],[6,7]] ], [ [[1,5,3,6,4]], [[1,6],[2,4]], [[3,4,6,5]] ]
		, [ [[5,6,7]], [[6,7]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], [[3,4]] ], 
	  [ [[1,2,3,4,5,6,7]], [[1,2],[3,6]] ], [ [[1,2,3,4,5]], [[3,4,5]], [[6,7]], [[4,5]] ], 
	  [ [[1,2,3,4,5]], [[4,5,6]] ], [ [[1,6,5,4,3]], [[2,4,3]], [[5,6]] ], 
	  [ [[1,2,3,4,5,6,7]], [[5,6,7]] ], [ [[1,2,3,4,5,6,7]], [[1,2]] ] ]
	   

	s8 :: [GroupGens]
	s8 = map getGroupGens [ [  ], [ [[7,8]] ], [ [[1,2],[3,4],[5,6],[7,8]] ], [ [[5,6],[7,8]] ], 
		  [ [[3,4],[5,6],[7,8]] ], [ [[6,7,8]] ], [ [[3,4,5],[6,7,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]] ], [ [[1,2],[3,4],[5,6],[7,8]], [[1,3],[2,4],[5,7],[6,8]] ], 
		  [ [[5,6],[7,8]], [[5,7,6,8]] ], [ [[7,8]], [[5,6]] ], [ [[5,6],[7,8]], [[1,2],[3,4]] ], 
		  [ [[5,6],[7,8]], [[3,4],[7,8]] ], [ [[7,8]], [[1,2],[3,4],[5,6]] ], 
		  [ [[5,6],[7,8]], [[1,2],[3,4],[5,7,6,8]] ], [ [[5,6],[7,8]], [[1,2],[3,4],[5,7],[6,8]] ], 
		  [ [[1,2],[3,4],[5,6],[7,8]], [[1,3,2,4],[5,7,6,8]] ], 
		  [ [[5,6],[7,8]], [[1,2],[3,4],[7,8]] ], [ [[3,4],[5,6],[7,8]], [[1,2],[5,7],[6,8]] ], 
		  [ [[7,8]], [[3,4],[5,6]] ], [ [[5,6],[7,8]], [[3,4],[5,7,6,8]] ], 
		  [ [[5,6],[7,8]], [[3,4],[5,7],[6,8]] ], [ [[4,5,6,7,8]] ], [ [[6,7,8]], [[7,8]] ], 
		  [ [[7,8]], [[4,5,6]] ], [ [[7,8]], [[1,2,3],[4,5,6]] ], [ [[6,7,8]], [[4,5],[7,8]] ], 
		  [ [[3,4,5],[6,7,8]], [[3,6],[4,8],[5,7]] ], 
		  [ [[3,4,5],[6,7,8]], [[1,2],[3,6],[4,8],[5,7]] ], [ [[6,7,8]], [[2,3],[4,5]] ], 
		  [ [[6,7,8]], [[2,3],[4,5],[7,8]] ], [ [[3,4],[5,6],[7,8]], [[3,5,7],[4,6,8]] ], 
		  [ [[3,4,5],[6,7,8]], [[1,2],[4,5],[7,8]] ], 
		  [ [[3,4,5],[6,7,8]], [[1,2],[3,6],[4,7],[5,8]] ], [ [[3,4,5],[6,7,8]], [[4,5],[7,8]] ], 
		  [ [[2,3,4,5,6,7,8]] ], 
		  [ [[1,2],[3,4],[5,6],[7,8]], [[1,3],[2,4],[5,7],[6,8]], [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[5,6],[7,8]], [[3,4],[7,8]], [[1,2],[7,8]] ], 
		  [ [[1,2],[3,4],[5,6],[7,8]], [[1,3,2,4],[5,7,6,8]], [[1,5,2,6],[3,8,4,7]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[1,2],[3,4]] ], [ [[7,8]], [[5,6]], [[5,7],[6,8]] ], 
		  [ [[5,6],[7,8]], [[1,2],[3,4]], [[1,3],[2,4],[5,7],[6,8]] ], 
		  [ [[5,6],[7,8]], [[1,2],[3,4]], [[1,3,2,4],[5,7,6,8]] ], [ [[7,8]], [[5,6]], [[3,4]] ], 
		  [ [[7,8]], [[3,4],[5,6]], [[3,5],[4,6]] ], [ [[7,8]], [[3,4],[5,6]], [[1,2],[5,6]] ], 
		  [ [[5,6],[7,8]], [[3,4],[5,7],[6,8]], [[1,2],[5,7],[6,8]] ], 
		  [ [[5,6],[7,8]], [[5,7,6,8]], [[1,2],[3,4]] ], 
		  [ [[5,6],[7,8]], [[5,7,6,8]], [[1,2],[3,4],[7,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[1,2],[3,4],[7,8]] ], 
		  [ [[5,6],[7,8]], [[3,4],[5,7,6,8]], [[1,2],[5,7,6,8]] ], 
		  [ [[7,8]], [[5,6]], [[1,2],[3,4]] ], [ [[7,8]], [[5,6]], [[1,2],[3,4],[5,7],[6,8]] ], 
		  [ [[5,6],[7,8]], [[1,2],[3,4]], [[1,3],[2,4],[5,7,6,8]] ], 
		  [ [[1,2],[3,4],[5,6],[7,8]], [[1,3],[2,4],[5,7],[6,8]], [[1,5,2,6],[3,7,4,8]] ], 
		  [ [[1,2],[3,4],[5,6],[7,8]], [[1,3],[2,4],[5,7],[6,8]], [[1,5],[2,6],[3,8],[4,7]] ], 
		  [ [[7,8]], [[3,4],[5,6]], [[1,2],[3,5,4,6]] ], 
		  [ [[3,4],[5,6],[7,8]], [[1,2],[5,7],[6,8]], [[1,3],[2,4],[6,7]] ], 
		  [ [[5,6],[7,8]], [[3,4],[7,8]], [[1,2],[5,7],[6,8]] ], 
		  [ [[7,8]], [[3,4],[5,6]], [[1,2],[3,5],[4,6]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[3,4],[7,8]] ], 
		  [ [[5,6],[7,8]], [[3,4],[7,8]], [[1,2],[5,7,6,8]] ], 
		  [ [[5,6],[7,8]], [[3,4],[5,7],[6,8]], [[1,2],[5,7,6,8]] ], 
		  [ [[7,8]], [[5,6]], [[3,4],[5,7],[6,8]] ], 
		  [ [[1,2],[3,4],[5,6],[7,8]], [[1,3,2,4],[5,7,6,8]], [[1,5,3,7,2,6,4,8]] ], 
		  [ [[5,6],[7,8]], [[1,2],[3,4],[7,8]], [[1,3],[2,4],[5,7],[6,8]] ], 
		  [ [[5,6],[7,8]], [[1,2],[3,4]], [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[7,8]], [[3,4],[5,6]], [[3,5,4,6]] ], [ [[5,6],[7,8]], [[5,7,6,8]], [[3,4],[7,8]] ], 
		  [ [[6,7,8]], [[3,4,5]] ], [ [[4,5,6,7,8]], [[5,8],[6,7]] ], [ [[7,8]], [[2,3,4,5,6]] ], 
		  [ [[4,5,6,7,8]], [[2,3],[5,8],[6,7]] ], [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]] ], 
		  [ [[6,7,8]], [[2,3],[4,5]], [[2,4],[3,5]] ], 
		  [ [[5,6],[7,8]], [[3,4],[7,8]], [[3,5,7],[4,6,8]] ], 
		  [ [[7,8]], [[1,2,3],[4,5,6]], [[1,4],[2,6],[3,5]] ], [ [[7,8]], [[4,5,6]], [[5,6]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[2,3,4],[6,7,8]] ], 
		  [ [[6,7,8]], [[2,3],[4,5]], [[2,4,3,5],[7,8]] ], 
		  [ [[6,7,8]], [[2,3],[4,5]], [[2,4],[3,5],[7,8]] ], [ [[6,7,8]], [[2,3],[4,5]], [[2,4,3,5]] ]
			, [ [[6,7,8]], [[4,5],[7,8]], [[2,3],[7,8]] ], [ [[6,7,8]], [[7,8]], [[2,3],[4,5]] ], 
		  [ [[7,8]], [[5,6]], [[2,3,4]] ], 
		  [ [[1,2],[3,4],[5,6],[7,8]], [[1,3],[2,4],[5,7],[6,8]], [[2,3,4],[6,7,8]] ], 
		  [ [[7,8]], [[1,2],[3,4],[5,6]], [[1,3,5],[2,4,6]] ], 
		  [ [[7,8]], [[1,2,3],[4,5,6]], [[2,3],[5,6]] ], 
		  [ [[3,5,4],[6,8,7]], [[3,6],[4,8],[5,7]], [[1,2],[4,5],[7,8]] ], 
		  [ [[3,4,5],[6,7,8]], [[4,5],[7,8]], [[1,2],[3,6],[4,7],[5,8]] ], 
		  [ [[3,4],[5,6],[7,8]], [[3,5,7],[4,6,8]], [[1,2],[5,7],[6,8]] ], 
		  [ [[7,8]], [[4,5,6]], [[2,3],[5,6]] ], 
		  [ [[3,4],[5,6],[7,8]], [[3,5,7],[4,6,8]], [[5,7],[6,8]] ], 
		  [ [[2,3,4,5,6,7,8]], [[3,8],[4,7],[5,6]] ], [ [[6,7,8]], [[1,2,3,4,5]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[1,2],[3,4]], [[1,3],[2,4]] ], 
		  [ [[7,8]], [[5,6]], [[3,4]], [[1,2]] ], [ [[7,8]], [[5,6]], [[1,2],[3,4]], [[1,3],[2,4]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[1,2],[3,4]], [[1,3,2,4]] ], 
		  [ [[5,6],[7,8]], [[3,4],[7,8]], [[1,2],[7,8]], [[1,3],[2,4],[5,7],[6,8]] ], 
		  [ [[5,6],[7,8]], [[3,4],[5,7,6,8]], [[1,2],[5,7,6,8]], [[1,3],[2,4],[5,7],[6,8]] ], 
		  [ [[5,6],[7,8]], [[3,4],[7,8]], [[1,2],[7,8]], [[1,3],[2,4],[5,7,6,8]] ], 
		  [ [[5,6],[7,8]], [[5,7,6,8]], [[1,2],[3,4]], [[1,3,2,4]] ], 
		  [ [[5,6],[7,8]], [[3,4],[5,7],[6,8]], [[1,2],[5,7],[6,8]], [[1,3],[2,4],[7,8]] ], 
		  [ [[5,6],[7,8]], [[5,7,6,8]], [[3,4],[7,8]], [[1,2],[7,8]] ], 
		  [ [[5,6],[7,8]], [[5,7,6,8]], [[1,2],[3,4]], [[1,3,2,4],[7,8]] ], 
		  [ [[5,6],[7,8]], [[5,7,6,8]], [[1,2],[3,4]], [[1,3],[2,4],[7,8]] ], 
		  [ [[7,8]], [[5,6]], [[1,2],[3,4]], [[1,3,2,4],[5,7],[6,8]] ], 
		  [ [[5,6],[7,8]], [[1,2],[3,4]], [[1,3,2,4],[5,7,6,8]], [[1,5,3,7,2,6,4,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[3,4],[7,8]], [[1,2],[7,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[1,2],[3,4]], [[1,3],[2,4],[7,8]] ], 
		  [ [[5,6],[7,8]], [[1,2],[3,4]], [[1,3],[2,4],[5,7],[6,8]], [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[7,8]], [[5,6]], [[1,2],[3,4]], [[1,3,2,4]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[1,2],[3,4]], [[1,3,2,4],[7,8]] ], 
		  [ [[5,6],[7,8]], [[3,4],[5,7],[6,8]], [[1,2],[5,7],[6,8]], [[1,3],[2,4],[5,7,6,8]] ], 
		  [ [[7,8]], [[5,6]], [[3,4],[5,7],[6,8]], [[1,2],[5,7],[6,8]] ], 
		  [ [[5,6]], [[7,8]], [[5,7],[6,8]], [[1,2],[3,4]] ], 
		  [ [[5,6],[7,8]], [[1,2],[3,4]], [[1,3,2,4],[5,7,6,8]], [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[7,8]], [[5,6]], [[1,2],[3,4]], [[1,3],[2,4],[5,7],[6,8]] ], 
		  [ [[5,6],[7,8]], [[1,2],[3,4]], [[1,3],[2,4],[5,7],[6,8]], [[1,5,3,7],[2,6,4,8]] ], 
		  [ [[7,8]], [[5,6]], [[3,4]], [[1,2],[5,7],[6,8]] ], 
		  [ [[5,6]], [[7,8]], [[5,7],[6,8]], [[3,4]] ], 
		  [ [[3,4],[5,6],[7,8]], [[1,2],[5,7],[6,8]], [[1,3],[2,4],[6,7]], [[1,5,2,8],[3,6,4,7]] ], 
		  [ [[3,4],[5,6],[7,8]], [[1,2],[5,7],[6,8]], [[1,3],[2,4],[6,7]], [[1,5],[2,8],[3,6],[4,7]] ],
		  [ [[7,8]], [[3,4],[5,6]], [[3,5],[4,6]], [[1,2],[5,6]] ], 
		  [ [[7,8]], [[3,4],[5,6]], [[3,5,4,6]], [[1,2],[5,6]] ], [ [[7,8]], [[4,5,6]], [[1,2,3]] ], 
		  [ [[6,7,8]], [[3,4,5]], [[1,2],[4,5],[7,8]] ], [ [[6,7,8]], [[3,4,5]], [[4,5],[7,8]] ], 
		  [ [[6,7,8]], [[3,4,5]], [[3,6],[4,7],[5,8]] ], [ [[6,7,8]], [[7,8]], [[3,4,5]] ], 
		  [ [[6,7,8]], [[3,4,5]], [[1,2],[3,6],[4,7],[5,8]] ], [ [[6,7,8]], [[4,5],[7,8]], [[1,2,3]] ]
			, [ [[4,5,6,7,8]], [[5,8],[6,7]], [[5,6,8,7]] ], 
		  [ [[4,5,6,7,8]], [[5,8],[6,7]], [[2,3],[5,6,8,7]] ], 
		  [ [[7,8]], [[2,3,4,5,6]], [[3,6],[4,5]] ], [ [[2,3,4,5,6,7,8]], [[3,4,6],[5,8,7]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[7,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[1,2],[3,4],[7,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[1,2],[3,4]] ], 
		  [ [[6,7,8]], [[7,8]], [[2,3],[4,5]], [[2,4],[3,5]] ], 
		  [ [[3,4],[7,8]], [[3,4],[5,6]], [[3,5,7],[4,6,8]], [[5,7,6,8]] ], 
		  [ [[3,4],[7,8]], [[3,4],[5,6]], [[3,5,7],[4,6,8]], [[1,2],[5,7],[6,8]] ], 
		  [ [[7,8]], [[5,6]], [[3,4]], [[3,5,7],[4,6,8]] ], 
		  [ [[3,4],[7,8]], [[3,4],[5,6]], [[3,5,7],[4,6,8]], [[1,2],[5,7,6,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[3,4],[7,8]] ], 
		  [ [[3,4],[7,8]], [[3,4],[5,6]], [[3,5,7],[4,6,8]], [[1,2],[7,8]] ], 
		  [ [[7,8]], [[3,4],[5,6]], [[3,5],[4,6]], [[4,5,6]] ], 
		  [ [[7,8]], [[3,4],[5,6]], [[1,2],[5,6]], [[1,3,5],[2,4,6]] ], 
		  [ [[3,4],[7,8]], [[3,4],[5,6]], [[3,5,7],[4,6,8]], [[5,7],[6,8]] ], 
		  [ [[7,8]], [[5,6]], [[2,3,4]], [[3,4],[5,7],[6,8]] ], 
		  [ [[5,6]], [[7,8]], [[5,7],[6,8]], [[2,3,4]] ], [ [[7,8]], [[5,6]], [[2,3,4]], [[3,4]] ], 
		  [ [[1,2],[3,4],[5,6],[7,8]], [[1,3],[2,4],[5,7],[6,8]], [[2,3,4],[6,7,8]], 
			  [[1,5],[2,6],[3,8],[4,7]] ], 
		  [ [[6,7,8]], [[4,5],[7,8]], [[2,3],[7,8]], [[2,4],[3,5],[7,8]] ], 
		  [ [[6,7,8]], [[7,8]], [[2,3],[4,5]], [[2,4,3,5]] ], 
		  [ [[1,2],[3,4],[5,6],[7,8]], [[1,3],[2,4],[5,7],[6,8]], [[2,3,4],[6,7,8]], 
			  [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[1,2],[3,4],[5,6],[7,8]], [[1,3],[2,4],[5,7],[6,8]], [[2,3,4],[6,7,8]], [[3,4],[7,8]] ], 
		  [ [[1,2],[3,4],[5,6],[7,8]], [[1,3,2,4],[5,7,6,8]], [[1,5,2,6],[3,8,4,7]], 
			  [[3,5,7],[4,6,8]] ], [ [[6,7,8]], [[4,5],[7,8]], [[2,3],[7,8]], [[2,4],[3,5]] ], 
		  [ [[7,8]], [[1,2],[3,4],[5,6]], [[1,3,5],[2,4,6]], [[3,5],[4,6]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[2,3,4],[6,7,8]], [[3,4],[7,8]] ], 
		  [ [[6,7,8]], [[1,2,3,4,5]], [[2,5],[3,4],[7,8]] ], [ [[6,7,8]], [[7,8]], [[1,2,3,4,5]] ], 
		  [ [[6,7,8]], [[1,2,3,4,5]], [[2,5],[3,4]] ], 
		  [ [[5,6],[7,8]], [[3,4],[7,8]], [[1,2],[7,8]], [[1,3],[2,4],[5,7],[6,8]], 
			  [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[5,6]], [[7,8]], [[5,7],[6,8]], [[1,2],[3,4]], [[1,3],[2,4]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[1,2],[3,4]], [[1,3],[2,4]], [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[5,6],[7,8]], [[5,7,6,8]], [[3,4],[7,8]], [[1,2],[7,8]], [[1,3],[2,4],[7,8]] ], 
		  [ [[5,6],[7,8]], [[3,4],[7,8]], [[1,2],[7,8]], [[1,3],[2,4],[5,7],[6,8]], 
			  [[1,5],[2,6],[3,7,4,8]] ], 
		  [ [[5,6],[7,8]], [[3,4],[7,8]], [[1,2],[7,8]], [[1,3],[2,4],[5,7],[6,8]], 
			  [[1,5,3,7,2,6,4,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[3,4],[7,8]], [[1,2],[7,8]], [[1,3],[2,4]] ], 
		  [ [[7,8]], [[5,6]], [[3,4]], [[1,2]], [[1,3],[2,4],[5,7],[6,8]] ], 
		  [ [[5,6],[7,8]], [[3,4],[7,8]], [[1,2],[7,8]], [[1,3],[2,4],[5,7],[6,8]], 
			  [[1,5,3,7],[2,6,4,8]] ], 
		  [ [[5,6],[7,8]], [[5,7,6,8]], [[1,2],[3,4]], [[1,3,2,4]], [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[5,6],[7,8]], [[1,2],[5,8,6,7]], [[3,4],[5,8,6,7]], [[1,3],[2,4],[5,7],[6,8]], 
			  [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[7,8]], [[5,6]], [[3,4],[5,7],[6,8]], [[1,2],[5,7],[6,8]], [[1,3],[2,4]] ], 
		  [ [[7,8]], [[5,6]], [[3,4],[5,7],[6,8]], [[1,2],[5,7],[6,8]], [[1,3],[2,4],[5,7],[6,8]] ], 
		  [ [[5,6]], [[7,8]], [[5,7],[6,8]], [[3,4]], [[1,2]] ], 
		  [ [[5,6],[7,8]], [[1,2],[5,8],[6,7]], [[3,4],[5,8],[6,7]], [[1,3],[2,4],[7,8]], 
			  [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[5,6]], [[7,8]], [[5,7],[6,8]], [[1,2],[3,4]], [[1,3,2,4]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[3,4],[7,8]], [[1,2],[7,8]], [[1,3],[2,4],[7,8]] ], 
		  [ [[6,7,8]], [[3,4,5]], [[4,5],[7,8]], [[1,2],[3,6],[4,7],[5,8]] ], 
		  [ [[7,8]], [[4,5,6]], [[1,2,3]], [[2,3],[5,6]] ], 
		  [ [[6,7,8]], [[2,3],[4,5]], [[2,4],[3,5]], [[3,4,5]] ], 
		  [ [[6,7,8]], [[3,4,5]], [[4,5],[7,8]], [[3,6],[4,7,5,8]] ], 
		  [ [[6,7,8]], [[3,4,5]], [[4,5],[7,8]], [[1,2],[3,6],[4,7,5,8]] ], 
		  [ [[6,7,8]], [[3,4,5]], [[4,5],[7,8]], [[3,6],[4,7],[5,8]] ], 
		  [ [[6,7,8]], [[7,8]], [[3,4,5]], [[4,5]] ], 
		  [ [[6,7,8]], [[4,5],[7,8]], [[1,2,3]], [[2,3],[7,8]] ], 
		  [ [[3,4,5]], [[6,7,8]], [[3,6],[4,7],[5,8]], [[1,2],[4,5],[7,8]] ], 
		  [ [[6,7,8]], [[7,8]], [[3,4,5]], [[1,2],[4,5]] ], 
		  [ [[7,8]], [[4,5,6]], [[1,2,3]], [[1,4],[2,5],[3,6]] ], 
		  [ [[7,8]], [[4,5,6]], [[5,6]], [[1,2,3]] ], 
		  [ [[7,8]], [[2,3,4,5,6]], [[3,6],[4,5]], [[3,4,6,5]] ], 
		  [ [[2,3,4,5,6,7,8]], [[3,4,6],[5,8,7]], [[3,8],[4,7],[5,6]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[1,2],[3,4]], [[1,3],[2,4]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4],[6,7,8]] ], 
		  [ [[7,8]], [[5,6]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[1,2],[3,4]], [[1,3],[2,4],[7,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[7,8]], [[1,2],[3,4]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[3,4],[7,8]], [[1,2],[7,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[1,2],[3,4]], [[1,3,2,4],[7,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[1,2],[3,4]], [[1,3,2,4]] ], 
		  [ [[3,4],[7,8]], [[3,4],[5,6]], [[3,5,7],[4,6,8]], [[5,7,6,8]], [[1,2],[7,8]] ], 
		  [ [[3,4],[7,8]], [[3,4],[5,6]], [[3,5,7],[4,6,8]], [[5,7],[6,8]], [[1,2],[7,8]] ], 
		  [ [[3,4]], [[7,8]], [[5,6]], [[3,5,7],[4,6,8]], [[1,2],[5,7],[6,8]] ], 
		  [ [[7,8]], [[3,4],[5,6]], [[3,5],[4,6]], [[4,5,6]], [[1,2],[5,6]] ], 
		  [ [[7,8]], [[3,4],[5,6]], [[3,5],[4,6]], [[4,5,6]], [[5,6]] ], 
		  [ [[3,4]], [[7,8]], [[5,6]], [[3,5,7],[4,6,8]], [[1,2]] ], 
		  [ [[7,8]], [[1,2],[5,6]], [[1,2],[3,4]], [[1,3,5],[2,4,6]], [[3,5],[4,6]] ], 
		  [ [[3,4]], [[7,8]], [[5,6]], [[3,5,7],[4,6,8]], [[5,7],[6,8]] ], 
		  [ [[7,8]], [[1,2],[5,6]], [[1,2],[3,4]], [[1,3,5],[2,4,6]], [[3,5,4,6]] ], 
		  [ [[5,6]], [[7,8]], [[5,7],[6,8]], [[2,3,4]], [[3,4]] ], 
		  [ [[1,2],[3,4],[5,6],[7,8]], [[1,3],[2,4],[5,7],[6,8]], [[2,3,4],[6,7,8]], [[3,4],[7,8]], 
			  [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[1,2],[3,4],[5,6],[7,8]], [[1,7,2,8],[3,5,4,6]], [[1,3,2,4],[5,7,6,8]], 
			  [[3,5,7],[4,6,8]], [[3,4],[5,8],[6,7]] ], 
		  [ [[1,2],[3,4],[5,6],[7,8]], [[1,3],[2,4],[5,7],[6,8]], [[1,5],[2,6],[3,7],[4,8]], 
			  [[2,3,5,4,7,8,6]] ], [ [[1,2,3,4,5]], [[3,4,5]] ], 
		  [ [[1,2,3,4,6]], [[1,4],[5,6]] ], [ [[6,7,8]], [[1,2,3,4,5]], [[2,5],[3,4]], [[2,3,5,4]] ]
			, [ [[6,7,8]], [[1,2,3,4,5]], [[2,5],[3,4]], [[2,3,5,4],[7,8]] ], 
		  [ [[6,7,8]], [[7,8]], [[1,2,3,4,5]], [[2,5],[3,4]] ], 
		  [ [[7,8]], [[5,6]], [[3,4]], [[1,2]], [[1,3],[2,4],[5,7],[6,8]], [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[5,6]], [[7,8]], [[5,7],[6,8]], [[3,4]], [[1,2]], [[1,3],[2,4]] ], 
		  [ [[5,6],[7,8]], [[5,8,6,7]], [[1,2],[5,6]], [[3,4],[5,6]], [[1,3],[2,4],[5,6]], 
			  [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[7,8]], [[5,6]], [[3,4]], [[1,2]], [[1,3],[2,4],[5,7],[6,8]], [[1,5,3,7],[2,6,4,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[1,2],[5,6]], [[3,4],[5,6]], [[1,3],[2,4]], 
			  [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[5,6],[7,8]], [[5,8,6,7]], [[1,2],[5,6]], [[3,4],[5,6]], [[1,3],[2,4],[5,6]], 
			  [[1,5],[2,6],[3,7,4,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[1,2],[5,6]], [[3,4],[5,6]], [[1,3],[2,4]], 
			  [[1,5],[2,6],[3,7,4,8]] ], 
		  [ [[6,7,8]], [[2,3],[4,5]], [[2,4],[3,5]], [[3,4,5]], [[4,5]] ], 
		  [ [[7,8]], [[4,5,6]], [[5,6]], [[1,2,3]], [[2,3]] ], 
		  [ [[6,7,8]], [[7,8]], [[3,4,5]], [[4,5]], [[1,2],[3,6],[4,7],[5,8]] ], 
		  [ [[7,8]], [[4,5,6]], [[1,2,3]], [[2,3],[5,6]], [[1,4],[2,5],[3,6]] ], 
		  [ [[6,7,8]], [[4,5],[7,8]], [[1,2,3]], [[2,3],[7,8]], [[1,6],[2,7,3,8]] ], 
		  [ [[6,7,8]], [[4,5],[7,8]], [[1,2,3]], [[2,3],[7,8]], [[1,6],[2,7],[3,8]] ], 
		  [ [[6,7,8]], [[7,8]], [[3,4,5]], [[4,5]], [[3,6],[4,7],[5,8]] ], 
		  [ [[6,7,8]], [[2,3],[4,5]], [[2,4],[3,5]], [[3,4,5]], [[4,5],[7,8]] ], 
		  [ [[7,8]], [[4,5,6]], [[1,2,3]], [[2,3],[5,6]], [[1,4],[2,5,3,6]] ], 
		  [ [[6,7,8]], [[7,8]], [[2,3],[4,5]], [[2,4],[3,5]], [[3,4,5]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4],[6,7,8]], 
			  [[1,5],[2,6],[3,8],[4,7]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[7,8]], [[1,2],[3,4]], [[1,3],[2,4]] ], 
		  [ [[5,6],[7,8]], [[3,4],[7,8]], [[1,2],[7,8]], [[1,3],[2,4],[5,7],[6,8]], 
			  [[1,5],[2,6],[3,7],[4,8]], [[3,5,7],[4,6,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[3,4],[7,8]], [[1,2],[7,8]], [[1,3],[2,4]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[3,4],[7,8]], [[1,2],[7,8]], [[1,3],[2,4],[7,8]] ]
			, [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[7,8]], [[1,2],[3,4]], [[1,3,2,4]] ], 
		  [ [[7,8]], [[5,6]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], [[3,4],[5,7],[6,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4],[6,7,8]], 
			  [[3,4],[7,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4],[6,7,8]], 
			  [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[7,8]], [[5,6]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], [[3,4]] ], 
		  [ [[5,6]], [[7,8]], [[5,7],[6,8]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]] ], 
		  [ [[3,4]], [[7,8]], [[5,6]], [[3,5,7],[4,6,8]], [[5,7],[6,8]], [[1,2]] ], 
		  [ [[1,2,3,4,5]], [[3,4,5]], [[4,5]] ], [ [[1,2,3,4,6]], [[1,4],[5,6]], [[7,8]] ], 
		  [ [[1,2,3,4,6]], [[1,4],[5,6]], [[3,4,6,5]] ], [ [[1,2,3,4,5]], [[3,4,5]], [[4,5],[7,8]] ]
			, [ [[1,2,3,4,5]], [[3,4,5]], [[7,8]] ], 
		  [ [[1,2,3,4,6]], [[1,4],[5,6]], [[3,4,6,5],[7,8]] ], 
		  [ [[6,7,8]], [[7,8]], [[1,2,3,4,5]], [[2,5],[3,4]], [[2,3,5,4]] ], 
		  [ [[7,8]], [[5,6]], [[5,7],[6,8]], [[1,2]], [[3,4]], [[1,3],[2,4]], [[1,5],[2,6],[3,7],[4,8]] ]
			, [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]] ], 
		  [ [[7,8]], [[4,5,6]], [[5,6]], [[1,2,3]], [[2,3]], [[1,4],[2,5],[3,6]] ], 
		  [ [[6,7,8]], [[7,8]], [[2,3],[4,5]], [[2,4],[3,5]], [[3,4,5]], [[4,5]] ], 
		  [ [[1,2,3,4,5,6,8]], [[1,2,4],[3,6,5]], [[1,6],[2,3],[4,5],[7,8]] ], 
		  [ [[1,2,3,4,5,6,7]], [[1,2],[3,6]] ], 
		  [ [[1,3],[2,4],[5,7],[6,8]], [[1,5],[2,6],[3,7],[4,8]], [[1,4],[2,3],[5,8],[6,7]], 
			  [[2,3,5,4,7,8,6]], [[3,5,7],[4,6,8]] ], [ [[1,2,3,4,5]], [[3,4,5]], [[6,7,8]] ], 
		  [ [[5,6],[7,8]], [[3,4],[7,8]], [[1,2],[7,8]], [[1,4],[2,3],[5,8],[6,7]], 
			  [[1,6],[2,5],[3,8],[4,7]], [[3,5,8],[4,6,7]], [[5,7],[6,8]] ], 
		  [ [[5,6],[7,8]], [[3,4],[7,8]], [[1,2],[7,8]], [[1,4],[2,3],[5,8],[6,7]], 
			  [[1,6],[2,5],[3,8],[4,7]], [[3,5,8],[4,6,7]], [[5,7,6,8]] ], 
		  [ [[7,8]], [[5,6]], [[3,4]], [[1,2]], [[1,3],[2,4],[5,7],[6,8]], [[1,5],[2,6],[3,7],[4,8]], 
			  [[3,5,7],[4,6,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4],[6,7,8]], 
			  [[3,4],[7,8]], [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[5,6]], [[7,8]], [[5,7],[6,8]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], [[3,4]] ], 
		  [ [[1,2,3,4,6]], [[1,4],[5,6]], [[7,8]], [[3,4,6,5]] ], 
		  [ [[1,2,3,4,5]], [[3,4,5]], [[7,8]], [[4,5]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[5,7,6]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], 
			  [[3,4],[7,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[7,8]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]] ],
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[5,7,6]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], 
			  [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[1,7,6,3,2,5,4]], [[1,7,3],[2,6,5]], [[1,5],[2,3],[4,8],[6,7]], [[3,4],[5,7],[6,8]] ], 
		  [ [[1,2,3,4,5]], [[4,5,6]] ], [ [[1,2,3,4,5]], [[3,4,5]], [[6,7,8]], [[4,5],[7,8]] ], 
		  [ [[1,2,3,4,5]], [[3,4,5]], [[6,7,8]], [[7,8]] ], 
		  [ [[1,2,3,4,5]], [[3,4,5]], [[6,7,8]], [[4,5]] ], 
		  [ [[7,8]], [[5,6]], [[3,4]], [[1,2]], [[1,3],[2,4],[5,7],[6,8]], [[1,5],[2,6],[3,7],[4,8]], 
			  [[3,5,7],[4,6,8]], [[5,7],[6,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[5,7,6]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], 
			  [[3,4],[7,8]], [[1,5],[2,6],[3,7,4,8]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[6,7,8]], [[7,8]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], 
			  [[3,4]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[5,7,6]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], 
			  [[3,4],[7,8]], [[1,5],[2,6],[3,7],[4,8]] ], [ [[1,2,3,4,5]], [[4,5,6]], [[7,8]] ], 
		  [ [[1,2,3,4,5]], [[4,5,6]], [[5,6]] ], [ [[1,2,3,4,5]], [[4,5,6]], [[5,6],[7,8]] ], 
		  [ [[1,2,3,4,5]], [[3,4,5]], [[6,7,8]], [[7,8]], [[4,5]] ], 
		  [ [[5,6],[7,8]], [[5,7],[6,8]], [[5,7,6]], [[5,6]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], 
			  [[3,4]], [[1,5],[2,6],[3,7],[4,8]] ], 
		  [ [[1,8],[2,3],[4,5],[6,7]], [[1,3],[2,8],[4,6],[5,7]], [[1,5],[2,6],[3,7],[4,8]], 
			  [[1,2,6,3,4,5,7]], [[1,2,3],[4,6,5]], [[1,2],[5,6]] ], 
		  [ [[1,2,3,4,5]], [[4,5,6]], [[7,8]], [[5,6]] ], [ [[1,2,3,4,5,6,7]], [[5,6,7]] ], 
		  [ [[1,7,6,5,4,2,3]], [[2,3,4]], [[6,7]] ], [ [[1,2,3,4,5,6,7]], [[6,7,8]] ], 
		  [ [[1,2,3,4,5,6,7,8]], [[1,2]] ] ]

	  
