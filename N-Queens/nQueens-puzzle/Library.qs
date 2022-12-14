namespace nQueens_puzzle {
    open Microsoft.Quantum.Arrays;  
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Math;

    // Prepare for W state for each row to ensure that each row has exactly one queen
    operation prepareWState (register: Qubit[], nQueens: Int) : Unit is Adj {
        let splited = Chunks(nQueens, register);
        
        for row in 0 .. nQueens - 1 {
            Ry(2.0 * ArcSin(1.0 / Sqrt(IntAsDouble(nQueens))), splited[row][0]);
            for col in 1 .. nQueens - 1 {
                ControlledOnInt(0, Ry(2.0 * ArcSin(1.0 / Sqrt(IntAsDouble(nQueens - col))), _))(splited[row][0 .. col - 1], splited[row][col]);
            }
        }
    }

    // The constraint only check column and diagonal because the input registers are already matched the row contraint.
    operation OracleNQueensConstraint (register: Qubit[], target: Qubit) : Unit is Adj{
        // 0  1  2  3
        // 4  5  6  7
        // 8  9  10 11
        // 12 13 14 15
        // a1 a2 a3
        
        let nQueens = Round(Sqrt(IntAsDouble(Length(register)))); // use Round instead of DoubleAsInt to prevent runtime error
        use auxQCol = Qubit[nQueens - 1];
        use auxQDia = Qubit[(nQueens * (nQueens - 1)) / 2];
        
        within {

            // Check column
            // If the sum of |1>, the queen, of the column is odd, flip the corresponding auxiliary Qubit
            // The W state ensures only one queen each row. If there is a column has more than one queen, then at least one another column has no queen. 
            // So, the only condition that achieve the column requirement is when all the auxiliary Qubits are flipped to |1> state.
            // Furthermore, we can check nQueens - 1 column only because it is impossible to have the unchecked one is |0> while all the others is |1>.
            for col in 0 .. nQueens - 2 {
                for row in col .. nQueens .. Length(register) - 1 {
                    Controlled X([register[row]], auxQCol[col]);
                }
            }

            // Check diagnol
            // The diagnol check will be conducted betweens rows, the total combination is N * (N - 1) / 2.
            // If the two rows exist two qubits along the diagnol, then it is impossible to have another pair in the same two rows.
            // So we need N * (N - 1) / 2 auxiliary Qubits only.
            // For example, the first row and the second row need to check 6 pairs - (0, 5), (1, 6), (2, 7), (1, 4), (2, 5), (3, 6) -
            // and then use CCNOT gate to store results in  the auxiliary Qubit.
            // If the two Qubit are the queens, flip the auxiliary Qubit to |0>.
            // If all the auxiliary Qubits are in |1> means they all meet the diagnol requirement.

            ApplyToEachA(X, auxQDia);
            for row1 in 0 .. nQueens .. Length(register) - nQueens - 1 {
                for row2 in row1 + nQueens .. nQueens .. Length(register) - nQueens {
                    let diff = (row2 - row1) / nQueens;
                    let auxIndex = (row1 / nQueens) * (2 * nQueens - (row1 / nQueens + 1)) / 2 + diff - 1;

                    // right diagnol
                    for col in 0 .. nQueens - diff - 1 {
                        CCNOT(register[row1 + col], register[row2 + col + diff], auxQDia[auxIndex]);
                    }

                    // left diagnol
                    for col in diff .. nQueens - 1 {    
                        CCNOT(register[row1 + col], register[row2 + col - diff], auxQDia[auxIndex]);
                    }
                }
            }
        } apply {
            // If each column and diagnol has exactly one queen, the two auxiliary Qubit will be all in |1>
            Controlled X(auxQCol + auxQDia, target);
        }
    }

    operation OracleConverterImpl (markingOracle : ((Qubit[], Qubit) => Unit is Adj), register : Qubit[]) : Unit is Adj{
        use target = Qubit();

        within {
            X(target);
            H(target);
        } apply {
            markingOracle(register, target);
        }
    }
    
    operation GroversSearchLoop (register : Qubit[], oracle : ((Qubit[], Qubit) => Unit is Adj), iterations : Int, statePrep : (Qubit[] => Unit is Adj)) : Unit {
        let phaseOracle = OracleConverterImpl(oracle, _);
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

    // To test Rigetti while it disallow control flow
    operation SolveNQueensPuzzle (nQueens: Int) : Result[] {
        let searchSpaceSize = nQueens ^ nQueens;

        use chessBoard = Qubit[nQueens * nQueens];
        use output = Qubit();

        let solutionsNumber = 2; // Should be modified for different nQueens
        let WStatePrep = prepareWState(_, nQueens);
        let iter = Round(PI() / 4.0 * Sqrt(IntAsDouble(searchSpaceSize) * 1.0 / IntAsDouble(solutionsNumber)));

        GroversSearchLoop(chessBoard, OracleNQueensConstraint, iter, WStatePrep);

        return ForEach(M, chessBoard);
    }

    operation SolveNQueensPuzzleLocal (nQueens: Int) : Unit {
        let searchSpaceSize = nQueens ^ nQueens;

        use chessBoard = Qubit[nQueens * nQueens];
        use output = Qubit();

        let solutionsNumber = 2; // Should be modified for different nQueens
        let WStatePrep = prepareWState(_, nQueens);
        let iter = Round(PI() / 4.0 * Sqrt(IntAsDouble(searchSpaceSize) * 1.0 / IntAsDouble(solutionsNumber)));

        mutable answer = [false, size = nQueens * nQueens];
        mutable correct = false;

        repeat {
            GroversSearchLoop(chessBoard, OracleNQueensConstraint, iter, WStatePrep);
            let res = MultiM(chessBoard);
            OracleNQueensConstraint(chessBoard, output);

            if (MResetZ(output) == One) {
                set correct = true;
                set answer = ResultArrayAsBoolArray(res);
            }
            ResetAll(chessBoard);
        } until (correct);

        let splitedResult = Chunks(nQueens, answer);
        mutable horizontalLine = "";
        
        for i in 0 .. nQueens - 1 {
            set horizontalLine += " -";
        }

        for row in 0 .. nQueens - 1 {
            Message(horizontalLine);
            mutable tempRow = "";
            for col in 0 .. nQueens - 1 {
                if splitedResult[row][col] == true {
                    set tempRow += "|Q";
                } else {
                    set tempRow += "| ";
                }
            }
            Message(tempRow + "|");
        }
        Message(horizontalLine);
    }
}
