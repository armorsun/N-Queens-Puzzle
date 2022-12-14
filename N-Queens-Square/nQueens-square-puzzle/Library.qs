namespace nQueens_square_puzzle {
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Math;
    
    function appendBitStrings (rows: Int, bitStrings: Bool[][], currentIndex: Int): (Bool[][], Bool[][]) {
        mutable zeroPrefix = [];
        mutable onePrefix = [];

        for row in 0 .. rows - 1 {
            if (bitStrings[row][currentIndex]) {
                set onePrefix = onePrefix + [bitStrings[row]];
            } else {
                set zeroPrefix = zeroPrefix + [bitStrings[row]];
            }
        }

        return (zeroPrefix, onePrefix);
    }

    // Prepare for the chessboard
    operation prepareNQueensSquareInitialState (register: Qubit[], bitStrings: Bool[][]): Unit is Adj {
        let nBitPerRow = Length(bitStrings[0]);
        let nRows = Length(register) / nBitPerRow;

        for i in 0 .. nBitPerRow .. Length(register) - nBitPerRow {
            prepareNQueensSquareColorInitialState([], register[i .. i + nBitPerRow - 1], bitStrings);
        }
    }

    // Prepare for the row state
    operation prepareNQueensSquareColorInitialState (currentBitString: Bool[], register: Qubit[], bitStrings: Bool[][]): Unit is Adj {
        let rows = Length(bitStrings);
        let currentIndex = Length(currentBitString);
        
        if (rows >= 1 and currentIndex < Length(register)) {
            let (zeroPrefix, onePrefix) = appendBitStrings(rows, bitStrings, currentIndex);
            let theta = ArcCos(Sqrt(IntAsDouble(Length(zeroPrefix)) / IntAsDouble(rows)));

            (ControlledOnBitString(currentBitString, Ry))(register[0 .. currentIndex - 1], (2.0 * theta, register[currentIndex]));
                
            prepareNQueensSquareColorInitialState(currentBitString + [false], register, zeroPrefix);
            prepareNQueensSquareColorInitialState(currentBitString + [true], register, onePrefix);
        }
    }

    // To test if the initial state is correct or not
    operation testNQueensSquareInitialState (): Unit {
        let nQueens = 5;
        let nBit = Ceiling(Lg(IntAsDouble(nQueens)));
    
        use queen = Qubit[nBit];

        mutable bitStrings = Chunks(nBit, [false, size = nQueens * nBit]);
        for i in 0 .. nQueens - 1 {
            set bitStrings w/= i <- IntAsBoolArray(i, nBit);
        }

        for i in 0 .. 50 {
            prepareNQueensSquareColorInitialState([], queen, bitStrings);
            let res = ResultArrayAsBoolArray(MultiM(queen));
            Message($"{res}");
            ResetAll(queen);
        }
    }

    operation OracleNQueensSquareConstraint (register: Qubit[], target: Qubit, nQueens: Int): Unit is Adj {
        // 0  1  2  3  4
        // 5  6  7  8  9
        // 10 11 12 13 14
        // 15 16 17 18 19
        // 20 21 22 23 24

        // 0 1 2 3 4   000 100 010 110 001
        // 3 4 0 1 2   110 001 000 100 010
        // 1 2 3 4 0   100 010 110 001 000
        // 4 0 1 2 3   001 000 100 010 110
        // 2 3 4 0 1   010 110 001 000 100

        let bitLength = Length(register) / (nQueens * nQueens); // The bit length needed for the color
        let rowIndexDiff = bitLength * nQueens;
        let rowCombination = (nQueens * (nQueens - 1)) / 2;
        
        use auxQCol = Qubit[nQueens * (nQueens - 1)];
        // The section is removed to execute column check only because of the lack of computing power
        //use auxQDia = Qubit[nQueens * rowCombination];

        within {
            // Check Column constraint
            for col in 0 .. bitLength .. rowIndexDiff - 2 * bitLength {
                for row in col .. rowIndexDiff .. Length(register) - 1 {
                    for bit in 0 .. nQueens - 1 {
                        ControlledOnBitString(IntAsBoolArray(bit, bitLength), X)(register[row .. row + bitLength - 1], auxQCol[nQueens * (col / bitLength) + bit]);
                    }
                }
            }

            // The section is removed to execute column check only because of the lack of computing power

            // Check Diagnol constraint
            // ApplyToEachA(X, auxQDia);
            // for row1 in 0 .. nQueens * bitLength .. Length(register) - nQueens * bitLength - 1 {
            //     for row2 in row1 + nQueens * bitLength .. nQueens * bitLength .. Length(register) - nQueens * bitLength {
            //         let diff = (row2 - row1) / (nQueens * bitLength);
            //         let auxIndex = (row1 / (nQueens * bitLength)) * (2 * nQueens - (row1 / (nQueens * bitLength) + 1)) / 2 + diff - 1;

            //         // right diagnol
            //         for col in 0 .. bitLength .. (nQueens - diff - 1) * bitLength {
            //             for bit in 0 .. nQueens - 1 {
            //                 ControlledOnBitString(IntAsBoolArray(bit, bitLength) + IntAsBoolArray(bit, bitLength), X)
            //                 (register[row1 + col .. row1 + col + bitLength - 1] +
            //                 register[row2 + col + diff * bitLength .. row2 + col + diff * bitLength + bitLength - 1],
            //                 auxQDia[auxIndex + bit * rowCombination]);
            //             }
            //         }

            //         // left diagnol
            //         for col in diff * bitLength .. bitLength .. (nQueens - 1) * bitLength {
            //             for bit in 0 .. nQueens - 1 {
            //                 ControlledOnBitString(IntAsBoolArray(bit, bitLength) + IntAsBoolArray(bit, bitLength), X)
            //                 (register[row1 + col .. row1 + col + bitLength - 1] +
            //                 register[row2 + col - diff * bitLength .. row2 + col - diff * bitLength + bitLength - 1],
            //                 auxQDia[auxIndex + bit * rowCombination]);
            //             }
            //         }
            //     }
            // }
        } apply {
            // The section is removed to execute column check only because of the lack of computing power
            // Controlled X(auxQCol + auxQDia, target);
            Controlled X(auxQCol, target);
        }
    }

    operation OracleConverterImpl (markingOracle: ((Qubit[], Qubit, Int) => Unit is Adj), register: Qubit[], nQueens: Int) : Unit is Adj {
        use target = Qubit();

        within {
            X(target);
            H(target);
        } apply {
            markingOracle(register, target, nQueens);
        }
    }
    
    operation GroversSearchLoop (register: Qubit[], oracle: ((Qubit[], Qubit, Int) => Unit is Adj), iterations: Int, statePrep: (Qubit[] => Unit is Adj), nQueens: Int): Unit {
        let phaseOracle = OracleConverterImpl(oracle, _, nQueens);
        statePrep(register);
            
        for i in 1 .. iterations {
            phaseOracle(register);
            within {
                Adjoint statePrep(register);
                ApplyToEachA(X, register);
            } apply {
                Controlled Z(Most(register), Tail(register));
            }
        }
    }

    function getBitsString (nQueens: Int): Bool[][] {
        mutable queens = [];
        let nBit = Ceiling(Lg(IntAsDouble(nQueens)));

        for i in 0 .. nQueens - 1 {
            set queens += [i];
        }

        let intStrings = getPermutations(queens, 0, new Int[][0]);
        mutable bitStrings = [];

        for row in 0 .. Length(intStrings) - 1 {
            for col in 0 .. Length(intStrings[0]) - 1 {
                set bitStrings += IntAsBoolArray(intStrings[row][col], nBit);
            }
        }

        return Chunks(nQueens * nBit, bitStrings);
    }

    // Get the permutation for different colors
    function getPermutations (queens: Int[], current: Int, result: Int[][]): Int[][] {
        mutable tempQueens = queens;
        mutable tempResult = result;

        if current == Length(queens) - 1 {
            set tempResult += [tempQueens];
        } else {
            for i in current .. Length(queens) - 1 {
                set tempQueens = Swapped(current, i, queens);
                set tempResult = getPermutations(tempQueens, current + 1, tempResult);
            }
        }

        return tempResult;
    }

    // To test Rigetti while it disallow control flow
    operation SolveNQueensSquarePuzzle (nQueens: Int) : Result[] {
        let searchSpaceSize = nQueens ^ nQueens;
        let nBit = Ceiling(Lg(IntAsDouble(nQueens)));

        use chessBoard = Qubit[nQueens * nQueens * nBit];
        let bitStrings = getBitsString(nQueens);

        use output = Qubit();

        let solutionsNumber = 12; // Should be modified for different nQueens
        let initialStatePrep = prepareNQueensSquareInitialState(_, bitStrings);
        let iter = Round(PI() / 4.0 * Sqrt(IntAsDouble(searchSpaceSize) * 1.0 / IntAsDouble(solutionsNumber)));

        GroversSearchLoop(chessBoard, OracleNQueensSquareConstraint, iter, initialStatePrep, nQueens);

        return ForEach(M, chessBoard);
    }

    operation SolveNQueensSquarePuzzleLocal (nQueens: Int): Unit {
        let searchSpaceSize = nQueens ^ nQueens;
        let nBit = Ceiling(Lg(IntAsDouble(nQueens)));

        use chessBoard = Qubit[nQueens * nQueens * nBit];
        let bitStrings = getBitsString(nQueens);
        
        use output = Qubit();

        let solutionsNumber = 12; // Should be modified for different nQueens
        let initialStatePrep = prepareNQueensSquareInitialState(_, bitStrings);
        let iter = Round(PI() / 4.0 * Sqrt(IntAsDouble(searchSpaceSize) * 1.0 / IntAsDouble(solutionsNumber)));

        mutable answer = [false, size = nQueens * nQueens * nBit];
        mutable correct = false;
        mutable horizontalLine = "";
        
        for i in 0 .. nQueens - 1 {
            set horizontalLine += " -";
        }

        repeat {
            GroversSearchLoop(chessBoard, OracleNQueensSquareConstraint, iter, initialStatePrep, nQueens);
            let res = MultiM(chessBoard);
            OracleNQueensSquareConstraint(chessBoard, output, nQueens);

            if (MResetZ(output) == One) {
                set correct = true;
                
                let splitedAnswer = Chunks(nBit, res);

                for row in 0 .. nQueens - 1 {
                    Message(horizontalLine);
                    mutable r = "";
                    for col in 0 .. nQueens - 1 {
                        set r = r + "|" + IntAsString(ResultArrayAsInt(splitedAnswer[row * nQueens + col]));
                    }
                    Message($"{r}" + "|");
                }
                Message(horizontalLine);
            }
            ResetAll(chessBoard);
        } until (correct);
    }


}
