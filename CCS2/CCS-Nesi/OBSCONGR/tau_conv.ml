% =========================================================================== %
% FILE          : tau_conv.ml                                                 %
% DESCRIPTION   : Conversions for applying the tau-laws of observation        %
%                 congruence                                                  %
%                                                                             %
% AUTHOR        : Monica Nesi                                                 %
% DATE          : July 1992                                                   %
% =========================================================================== %

% --------------------------------------------------------------------------- %
% Conversion for the application of the tau-law TAU1:                         %
%    |- !u E. OBS_CONGR(prefix u(prefix tau E))(prefix u E)                   %
% --------------------------------------------------------------------------- %
let OC_TAU1_CONV tm =
   is_prefix tm => 
    let u,t = args_prefix tm in 
    is_prefix t => 
     let u',t' = args_prefix t in  
     is_tau u' => SPECL [u; t'] TAU1 | 
     failwith `OC_TAU1_CONV` | 
    failwith `OC_TAU1_CONV` | 
   failwith `OC_TAU1_CONV`;; 

% --------------------------------------------------------------------------- %
% Conversion for the application of the tau-law TAU2:                         %
%    |- !E. OBS_CONGR(sum E(prefix tau E))(prefix tau E)                      %
% --------------------------------------------------------------------------- %
%let TAU2_CONV tm = 
% 

% --------------------------------------------------------------------------- %
% Conversion for the application of the tau-law TAU3:                         %
%    |- !u E E'.                                                              %
%        OBS_CONGR (sum(prefix u(sum E(prefix tau E')))(prefix u E'))         %
%                  (prefix u(sum E(prefix tau E')))                           %
% --------------------------------------------------------------------------- %
%let TAU3_CONV tm = 
% 
