using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using static System.Diagnostics.Debug;

using Microsoft.Quantum.Simulation.Core;
using Microsoft.Quantum.Simulation.Simulators;

namespace nQueens_square_puzzle
{
    static class Program
    {
        static async Task Main(string[] args)
        {
            using var sparseSim = new SparseSimulator();

            var nQueens = 3;
            var result = await SolveNQueensSquarePuzzleLocal.Run(sparseSim, nQueens);

        }
    }
}
