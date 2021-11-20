#pragma once

#define RTTI_CLASS_OF(TY, ENUM)               \
  static inline bool classof(const TY *Ref) { \
    return Ref->TyEnum == ENUM;               \
  }
