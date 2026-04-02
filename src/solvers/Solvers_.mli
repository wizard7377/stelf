module CsManager : module type of CsManager
module Cs : module type of Cs
module CsEqField : module type of CsEqField
module CsIneqField : module type of CsIneqField
module CsEqIntegers : module type of CsEqIntegers
module CsIneqIntegers : module type of CsIneqIntegers
module CsEqStrings : module type of CsEqStrings
module CsEqBools : module type of CsEqBools
module CsIntegersWord : module type of CsIntegersWord
include module type of Solvers_intf

module CSInstaller : CS_INSTALLER
