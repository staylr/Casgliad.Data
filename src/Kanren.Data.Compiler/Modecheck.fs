namespace Kanren.Data.Compiler

open Kanren.Data.Compiler.State

module Modecheck =
    type DepthNum = int
    type SeqNum = int
    type DelayGoalNum = { DepthNum: DepthNum; SeqNum: SeqNum }

    //type DelayInfo = { }


   // type ModeInfo = { ]
